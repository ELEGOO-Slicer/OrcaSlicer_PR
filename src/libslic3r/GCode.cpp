#include "BoundingBox.hpp"
#include "Config.hpp"
#include "Polygon.hpp"
#include "PrintConfig.hpp"
#include "libslic3r.h"
#include "I18N.hpp"
#include "GCode.hpp"
#include "Exception.hpp"
#include "ExtrusionEntity.hpp"
#include "EdgeGrid.hpp"
#include "Geometry/ConvexHull.hpp"
#include "GCode/PrintExtents.hpp"
#include "GCode/Thumbnails.hpp"
#include "GCode/WipeTower.hpp"
#include "ShortestPath.hpp"
#include "Print.hpp"
#include "Utils.hpp"
#include "ClipperUtils.hpp"
#include "libslic3r.h"
#include "LocalesUtils.hpp"
#include "libslic3r/format.hpp"
#include "Time.hpp"
#include "GCode/ExtrusionProcessor.hpp"
#include <algorithm>
#include <cmath>
#include <cstdlib>
#include <chrono>
#include <iostream>
#include <math.h>
#include <stdlib.h>
#include <string>
#include <utility>
#include <string_view>

#include <regex>
#include <boost/algorithm/string.hpp>
#include <boost/algorithm/string/find.hpp>
#include <boost/foreach.hpp>
#include <boost/filesystem.hpp>
#include <boost/log/trivial.hpp>
#include <boost/beast/core/detail/base64.hpp>

#include <boost/nowide/iostream.hpp>
#include <boost/nowide/cstdio.hpp>
#include <boost/nowide/cstdlib.hpp>

#include "SVG.hpp"

#include <tbb/parallel_for.h>
#include "calib.hpp"
// Intel redesigned some TBB interface considerably when merging TBB with their oneAPI set of libraries, see GH #7332.
// We are using quite an old TBB 2017 U7. Before we update our build servers, let's use the old API, which is deprecated in up to date TBB.
#if ! defined(TBB_VERSION_MAJOR)
    #include <tbb/version.h>
#endif
#if ! defined(TBB_VERSION_MAJOR)
    static_assert(false, "TBB_VERSION_MAJOR not defined");
#endif
#if TBB_VERSION_MAJOR >= 2021
    #include <tbb/parallel_pipeline.h>
    using slic3r_tbb_filtermode = tbb::filter_mode;
#else
    #include <tbb/pipeline.h>
    using slic3r_tbb_filtermode = tbb::filter;
#endif

#include <Shiny/Shiny.h>

#include "miniz_extension.hpp"

using namespace std::literals::string_view_literals;

#if 0
// Enable debugging and asserts, even in the release build.
#define DEBUG
#define _DEBUG
#undef NDEBUG
#endif

#include <assert.h>

namespace Slic3r {

    //! macro used to mark string used at localization,
    //! return same string
#define L(s) (s)
#define _(s) Slic3r::I18N::translate(s)

static const float g_min_purge_volume = 100.f;
static const float g_purge_volume_one_time = 135.f;
static const int g_max_flush_count = 4;
// static const size_t g_max_label_object = 64;

Vec2d travel_point_1;
Vec2d travel_point_2;
Vec2d travel_point_3;

static std::vector<Vec2d> get_path_of_change_filament(const Print& print)
{
    // give safe value in case there is no start_end_points in config
    std::vector<Vec2d> out_points;
    out_points.emplace_back(Vec2d(54, 0));
    out_points.emplace_back(Vec2d(54, 0));
    out_points.emplace_back(Vec2d(54, 245));

    // get the start_end_points from config (20, -3) (54, 245)
    Pointfs points = print.config().start_end_points.values;
    if (points.size() != 2)
        return out_points;

    Vec2d start_point  = points[0];
    Vec2d end_point    = points[1];

    // the cutter area size(18, 28)
    Pointfs excluse_area = print.config().bed_exclude_area.values;
    if (excluse_area.size() != 4)
        return out_points;

    double cutter_area_x = excluse_area[2].x() + 2;
    double cutter_area_y = excluse_area[2].y() + 2;

    double start_x_position = start_point.x();
    double end_x_position   = end_point.x();
    double end_y_position   = end_point.y();

    bool can_travel_form_left = true;

    // step 1: get the x-range intervals of all objects
    std::vector<std::pair<double, double>> object_intervals;
    for (PrintObject *print_object : print.objects()) {
        const PrintInstances &print_instances = print_object->instances();
        BoundingBoxf3 bounding_box = print_instances[0].model_instance->get_object()->bounding_box_exact();

        if (bounding_box.min.x() < start_x_position && bounding_box.min.y() < cutter_area_y)
            can_travel_form_left = false;

        std::pair<double, double> object_scope = std::make_pair(bounding_box.min.x() - 2, bounding_box.max.x() + 2);
        if (object_intervals.empty())
            object_intervals.push_back(object_scope);
        else {
            std::vector<std::pair<double, double>> new_object_intervals;
            bool intervals_intersect = false;
            std::pair<double, double>              new_merged_scope;
            for (auto object_interval : object_intervals) {
                if (object_interval.second >= object_scope.first && object_interval.first <= object_scope.second) {
                    if (intervals_intersect) {
                        new_merged_scope = std::make_pair(std::min(object_interval.first, new_merged_scope.first), std::max(object_interval.second, new_merged_scope.second));
                    } else { // it is the first intersection
                        new_merged_scope = std::make_pair(std::min(object_interval.first, object_scope.first), std::max(object_interval.second, object_scope.second));
                    }
                    intervals_intersect = true;
                } else {
                    new_object_intervals.push_back(object_interval);
                }
            }

            if (intervals_intersect) {
                new_object_intervals.push_back(new_merged_scope);
                object_intervals = new_object_intervals;
            } else
                object_intervals.push_back(object_scope);
        }
    }

    // step 2: get the available x-range
    std::sort(object_intervals.begin(), object_intervals.end(),
              [](const std::pair<double, double> &left, const std::pair<double, double> &right) {
            return left.first < right.first;
    });
    std::vector<std::pair<double, double>> available_intervals;
    double                                 start_position = 0;
    for (auto object_interval : object_intervals) {
        if (object_interval.first > start_position)
            available_intervals.push_back(std::make_pair(start_position, object_interval.first));
        start_position = object_interval.second;
    }
    available_intervals.push_back(std::make_pair(start_position, 255));

    // step 3: get the nearest path
    double new_path     = 255;
    for (auto available_interval : available_intervals) {
        if (available_interval.first > end_x_position) {
            double distance = available_interval.first - end_x_position;
            new_path        = abs(end_x_position - new_path) < distance ? new_path : available_interval.first;
            break;
        } else {
            if (available_interval.second >= end_x_position) {
                new_path = end_x_position;
                break;
            } else if (!can_travel_form_left && available_interval.second < start_x_position) {
                continue;
            } else {
                new_path     = available_interval.second;
            }
        }
    }

    // step 4: generate path points  (new_path == start_x_position means not need to change path)
    Vec2d out_point_1;
    Vec2d out_point_2;
    Vec2d out_point_3;
    if (new_path < start_x_position) {
        out_point_1 = Vec2d(start_x_position, cutter_area_y);
        out_point_2 = Vec2d(new_path, cutter_area_y);
        out_point_3 = Vec2d(new_path, end_y_position);
    } else {
        out_point_1 = Vec2d(new_path, 0);
        out_point_2 = Vec2d(new_path, 0);
        out_point_3 = Vec2d(new_path, end_y_position);
    }

    out_points.clear();
    out_points.emplace_back(out_point_1);
    out_points.emplace_back(out_point_2);
    out_points.emplace_back(out_point_3);

    return out_points;
}

// Only add a newline in case the current G-code does not end with a newline.
    static inline void check_add_eol(std::string& gcode)
    {
        if (!gcode.empty() && gcode.back() != '\n')
            gcode += '\n';
    }


    // Return true if tch_prefix is found in custom_gcode
    static bool custom_gcode_changes_tool(const std::string& custom_gcode, const std::string& tch_prefix, unsigned next_extruder)
    {
        bool ok = false;
        size_t from_pos = 0;
        size_t pos = 0;
        while ((pos = custom_gcode.find(tch_prefix, from_pos)) != std::string::npos) {
            if (pos + 1 == custom_gcode.size())
                break;
            from_pos = pos + 1;
            // only whitespace is allowed before the command
            while (--pos < custom_gcode.size() && custom_gcode[pos] != '\n') {
                if (!std::isspace(custom_gcode[pos]))
                    goto NEXT;
            }
            {
                // we should also check that the extruder changes to what was expected
                std::istringstream ss(custom_gcode.substr(from_pos, std::string::npos));
                unsigned num = 0;
                if (ss >> num)
                    ok = (num == next_extruder);
            }
        NEXT:;
        }
        return ok;
    }

    std::string OozePrevention::pre_toolchange(GCode& gcodegen)
    {
        std::string gcode;

        unsigned int extruder_id = gcodegen.writer().extruder()->id();
        const auto& filament_idle_temp = gcodegen.config().idle_temperature;
        if (filament_idle_temp.get_at(extruder_id) == 0) {
            // There is no idle temperature defined in filament settings.
            // Use the delta value from print config.
            if (gcodegen.config().standby_temperature_delta.value != 0) {
                // we assume that heating is always slower than cooling, so no need to block
                gcode += gcodegen.writer().set_temperature
                (this->_get_temp(gcodegen) + gcodegen.config().standby_temperature_delta.value, false, extruder_id);
                gcode.pop_back();
                gcode += " ;cooldown\n"; // this is a marker for GCodeProcessor, so it can supress the commands when needed
            }
        } else {
            // Use the value from filament settings. That one is absolute, not delta.
            gcode += gcodegen.writer().set_temperature(filament_idle_temp.get_at(extruder_id), false, extruder_id);
            gcode.pop_back();
            gcode += " ;cooldown\n"; // this is a marker for GCodeProcessor, so it can supress the commands when needed
        }

        return gcode;
    }

    std::string OozePrevention::post_toolchange(GCode& gcodegen)
    {
        return (gcodegen.config().standby_temperature_delta.value != 0) ?
            gcodegen.writer().set_temperature(this->_get_temp(gcodegen), true, gcodegen.writer().extruder()->id()) :
            std::string();
    }

    int OozePrevention::_get_temp(const GCode &gcodegen) const
    {
        // First layer temperature should be used when on the first layer (obviously) and when
        // "other layers" is set to zero (which means it should not be used).
        return (gcodegen.layer() == nullptr || gcodegen.layer()->id() == 0
             || gcodegen.config().nozzle_temperature.get_at(gcodegen.writer().extruder()->id()) == 0)
            ? gcodegen.config().nozzle_temperature_initial_layer.get_at(gcodegen.writer().extruder()->id())
            : gcodegen.config().nozzle_temperature.get_at(gcodegen.writer().extruder()->id());
    }
    
    // Orca:
    // Function to calculate the excess retraction length that should be retracted either before or after wiping
    // in order for the wipe operation to respect the filament retraction speed
    Wipe::RetractionValues Wipe::calculateWipeRetractionLengths(GCode& gcodegen, bool toolchange) {
        auto& writer = gcodegen.writer();
        auto& config = gcodegen.config();
        auto extruder = writer.extruder();
        auto extruder_id = extruder->id();
        auto last_pos = gcodegen.last_pos();
        
        // Declare & initialize retraction lengths
        double retraction_length_remaining = 0,
                retractionBeforeWipe = 0,
                retractionDuringWipe = 0;
        
        // initialise the remaining retraction amount with the full retraction amount.
        retraction_length_remaining = toolchange ? extruder->retract_length_toolchange() : extruder->retraction_length();
        
        // nothing to retract - return early
        if(retraction_length_remaining <=EPSILON) return {0.f,0.f};
        
        // calculate retraction before wipe distance from the user setting. Keep adding to this variable any excess retraction needed
        // to be performed before the wipe.
        retractionBeforeWipe = retraction_length_remaining * extruder->retract_before_wipe();
        retraction_length_remaining -= retractionBeforeWipe; // subtract it from the remaining retraction length
        
        // all of the retraction is to be done before the wipe
        if(retraction_length_remaining <=EPSILON) return {retractionBeforeWipe,0.f};
        
        // Calculate wipe speed
        double wipe_speed = config.role_based_wipe_speed ? writer.get_current_speed() / 60.0 : config.get_abs_value("wipe_speed");
        wipe_speed = std::max(wipe_speed, 10.0);

        // Process wipe path & calculate wipe path length
        double wipe_dist = scale_(config.wipe_distance.get_at(extruder_id));
        Polyline wipe_path = {last_pos};
        wipe_path.append(this->path.points.begin() + 1, this->path.points.end());
        double wipe_path_length = std::min(wipe_path.length(), wipe_dist);

        // Calculate the maximum retraction amount during wipe
        retractionDuringWipe = config.retraction_speed.get_at(extruder_id) * unscale_(wipe_path_length) / wipe_speed;
        // If the maximum retraction amount during wipe is too small, return 0 and retract everything prior to the wipe.
        if(retractionDuringWipe <= EPSILON) return {retractionBeforeWipe,0.f};
        
        // If the maximum retraction amount during wipe is greater than any remaining retraction length
        // return the remaining retraction length to be retracted during the wipe
        if (retractionDuringWipe - retraction_length_remaining > EPSILON) return {retractionBeforeWipe,retraction_length_remaining};
        
        // We will always proceed with incrementing the retraction amount before wiping with the difference
        // and return the maximum allowed wipe amount to be retracted during the wipe move
        retractionBeforeWipe += retraction_length_remaining - retractionDuringWipe;
        return {retractionBeforeWipe, retractionDuringWipe};
    }

    std::string Wipe::wipe(GCode& gcodegen,double length, bool toolchange, bool is_last)
    {
        std::string gcode;

        /*  Reduce feedrate a bit; travel speed is often too high to move on existing material.
            Too fast = ripping of existing material; too slow = short wipe path, thus more blob.  */
        double _wipe_speed = gcodegen.config().get_abs_value("wipe_speed");// gcodegen.writer().config.travel_speed.value * 0.8;
        if(gcodegen.config().role_based_wipe_speed)
            _wipe_speed = gcodegen.writer().get_current_speed() / 60.0;
        if(_wipe_speed < 10)
            _wipe_speed = 10;


        //SoftFever: allow 100% retract before wipe
        if (length >= 0)
        {
            /*  Calculate how long we need to travel in order to consume the required
                amount of retraction. In other words, how far do we move in XY at wipe_speed
                for the time needed to consume retraction_length at retraction_speed?  */
            // BBS
            double wipe_dist = scale_(gcodegen.config().wipe_distance.get_at(gcodegen.writer().extruder()->id()));
            
            /*  Take the stored wipe path and replace first point with the current actual position
                (they might be different, for example, in case of loop clipping).  */
            Polyline wipe_path;
            wipe_path.append(gcodegen.last_pos());
            wipe_path.append(
                this->path.points.begin() + 1,
                this->path.points.end()
            );

            wipe_path.clip_end(wipe_path.length() - wipe_dist);

            // subdivide the retraction in segments
            if (!wipe_path.empty()) {
                // BBS. Handle short path case.
                if (wipe_path.length() < wipe_dist) {
                    wipe_dist = wipe_path.length();
                    //BBS: avoid to divide 0
                    wipe_dist = wipe_dist < EPSILON ? EPSILON : wipe_dist;
                }

                // add tag for processor
                gcode += ";" + GCodeProcessor::reserved_tag(GCodeProcessor::ETags::Wipe_Start) + "\n";
                //BBS: don't need to enable cooling makers when this is the last wipe. Because no more cooling layer will clean this "_WIPE"
                //Softfever:
                std::string cooling_mark = "";
                if (gcodegen.enable_cooling_markers() && !is_last)
                    cooling_mark = /*gcodegen.config().role_based_wipe_speed ? ";_EXTERNAL_PERIMETER" : */";_WIPE";

                gcode += gcodegen.writer().set_speed(_wipe_speed * 60, "", cooling_mark);
                for (const Line& line : wipe_path.lines()) {
                    double segment_length = line.length();
                    double dE = length * (segment_length / wipe_dist);
                    //BBS: fix this FIXME
                    //FIXME one shall not generate the unnecessary G1 Fxxx commands, here wipe_speed is a constant inside this cycle.
                    // Is it here for the cooling markers? Or should it be outside of the cycle?
                    //gcode += gcodegen.writer().set_speed(wipe_speed * 60, "", gcodegen.enable_cooling_markers() ? ";_WIPE" : "");
                    gcode += gcodegen.writer().extrude_to_xy(
                        gcodegen.point_to_gcode(line.b),
                        -dE,
                        "wipe and retract"
                    );
                }
                // add tag for processor
                gcode += ";" + GCodeProcessor::reserved_tag(GCodeProcessor::ETags::Wipe_End) + "\n";
                gcodegen.set_last_pos(wipe_path.points.back());
            }

            // prevent wiping again on same path
            this->reset_path();
        }

        return gcode;
    }

    static inline Point wipe_tower_point_to_object_point(GCode& gcodegen, const Vec2f& wipe_tower_pt)
    {
        return Point(scale_(wipe_tower_pt.x() - gcodegen.origin()(0)), scale_(wipe_tower_pt.y() - gcodegen.origin()(1)));
    }

    std::string WipeTowerIntegration::append_tcr(GCode &gcodegen, const WipeTower::ToolChangeResult &tcr, int new_extruder_id, double z) const
    {
        if (new_extruder_id != -1 && new_extruder_id != tcr.new_tool)
            throw Slic3r::InvalidArgument("Error: WipeTowerIntegration::append_tcr was asked to do a toolchange it didn't expect.");

        std::string gcode;

        // Toolchangeresult.gcode assumes the wipe tower corner is at the origin (except for priming lines)
        // We want to rotate and shift all extrusions (gcode postprocessing) and starting and ending position
        float alpha = m_wipe_tower_rotation / 180.f * float(M_PI);

        auto transform_wt_pt = [&alpha, this](const Vec2f &pt) -> Vec2f {
            Vec2f out = Eigen::Rotation2Df(alpha) * pt;
            out += m_wipe_tower_pos;
            return out;
        };

        Vec2f start_pos = tcr.start_pos;
        Vec2f end_pos   = tcr.end_pos;
        if (!tcr.priming) {
            start_pos = transform_wt_pt(start_pos);
            end_pos   = transform_wt_pt(end_pos);
        }

        Vec2f wipe_tower_offset   = tcr.priming ? Vec2f::Zero() : m_wipe_tower_pos;
        float wipe_tower_rotation = tcr.priming ? 0.f : alpha;

        std::string tcr_rotated_gcode = post_process_wipe_tower_moves(tcr, wipe_tower_offset, wipe_tower_rotation);

        // BBS: add partplate logic
        Vec2f plate_origin_2d(m_plate_origin(0), m_plate_origin(1));

        // BBS: toolchange gcode will move to start_pos,
        // so only perform movement when printing sparse partition to support upper layer.
        // start_pos is the position in plate coordinate.
        if (!tcr.priming && tcr.is_finish_first) {
            // Move over the wipe tower.
            gcode += gcodegen.retract();
            gcodegen.m_avoid_crossing_perimeters.use_external_mp_once();
            gcode += gcodegen.travel_to(wipe_tower_point_to_object_point(gcodegen, start_pos + plate_origin_2d), erMixed,
                                        "Travel to a Wipe Tower");
            gcode += gcodegen.unretract();
        }

        // BBS: if needed, write the gcode_label_objects_end then priming tower, if the retract, didn't did it.
        gcodegen.m_writer.add_object_end_labels(gcode);

        double current_z = gcodegen.writer().get_position().z();
        if (z == -1.) // in case no specific z was provided, print at current_z pos
            z = current_z;
        if (!is_approx(z, current_z)) {
            gcode += gcodegen.writer().retract();
            gcode += gcodegen.writer().travel_to_z(z, "Travel down to the last wipe tower layer.");
            gcode += gcodegen.writer().unretract();
        }

        // Process the end filament gcode.
        std::string end_filament_gcode_str;
        if (gcodegen.writer().extruder() != nullptr) {
            // Process the custom filament_end_gcode in case of single_extruder_multi_material.
            unsigned int       old_extruder_id    = gcodegen.writer().extruder()->id();
            const std::string &filament_end_gcode = gcodegen.config().filament_end_gcode.get_at(old_extruder_id);
            if (gcodegen.writer().extruder() != nullptr && !filament_end_gcode.empty()) {
                end_filament_gcode_str = gcodegen.placeholder_parser_process("filament_end_gcode", filament_end_gcode, old_extruder_id);
                check_add_eol(end_filament_gcode_str);
            }
        }
        // BBS: increase toolchange count
        gcodegen.m_toolchange_count++;

        // BBS: should be placed before toolchange parsing
        std::string toolchange_retract_str = gcodegen.retract(true, false);
        check_add_eol(toolchange_retract_str);

        // Process the custom change_filament_gcode. If it is empty, provide a simple Tn command to change the filament.
        // Otherwise, leave control to the user completely.
        std::string        toolchange_gcode_str;
        const std::string &change_filament_gcode = gcodegen.config().change_filament_gcode.value;
        //        m_max_layer_z = std::max(m_max_layer_z, tcr.print_z);
        if (!change_filament_gcode.empty()) {
            DynamicConfig config;
            int           previous_extruder_id = gcodegen.writer().extruder() ? (int) gcodegen.writer().extruder()->id() : -1;
            config.set_key_value("previous_extruder", new ConfigOptionInt(previous_extruder_id));
            config.set_key_value("next_extruder", new ConfigOptionInt((int) new_extruder_id));
            config.set_key_value("layer_num", new ConfigOptionInt(gcodegen.m_layer_index));
            config.set_key_value("layer_z", new ConfigOptionFloat(tcr.print_z));
            config.set_key_value("toolchange_z", new ConfigOptionFloat(z));
            //            config.set_key_value("max_layer_z", new ConfigOptionFloat(m_max_layer_z));
            // BBS
            {
                GCodeWriter     &gcode_writer = gcodegen.m_writer;
                FullPrintConfig &full_config  = gcodegen.m_config;
                float old_retract_length = gcode_writer.extruder() != nullptr ? full_config.retraction_length.get_at(previous_extruder_id) :
                                                                                0;
                float new_retract_length = full_config.retraction_length.get_at(new_extruder_id);
                float old_retract_length_toolchange = gcode_writer.extruder() != nullptr ?
                                                          full_config.retract_length_toolchange.get_at(previous_extruder_id) :
                                                          0;
                float new_retract_length_toolchange = full_config.retract_length_toolchange.get_at(new_extruder_id);
                int   old_filament_temp             = gcode_writer.extruder() != nullptr ?
                                                          (gcodegen.on_first_layer() ?
                                                               full_config.nozzle_temperature_initial_layer.get_at(previous_extruder_id) :
                                                               full_config.nozzle_temperature.get_at(previous_extruder_id)) :
                                                          210;
                int   new_filament_temp = gcodegen.on_first_layer() ? full_config.nozzle_temperature_initial_layer.get_at(new_extruder_id) :
                                                                      full_config.nozzle_temperature.get_at(new_extruder_id);
                Vec3d nozzle_pos        = gcode_writer.get_position();

                float purge_volume  = tcr.purge_volume < EPSILON ? 0 : std::max(tcr.purge_volume, g_min_purge_volume);
                float filament_area = float((M_PI / 4.f) * pow(full_config.filament_diameter.get_at(new_extruder_id), 2));
                float purge_length  = purge_volume / filament_area;

                int old_filament_e_feedrate = gcode_writer.extruder() != nullptr ?
                                                  (int) (60.0 * full_config.filament_max_volumetric_speed.get_at(previous_extruder_id) /
                                                         filament_area) :
                                                  200;
                old_filament_e_feedrate     = old_filament_e_feedrate == 0 ? 100 : old_filament_e_feedrate;
                int new_filament_e_feedrate = (int) (60.0 * full_config.filament_max_volumetric_speed.get_at(new_extruder_id) /
                                                     filament_area);
                new_filament_e_feedrate     = new_filament_e_feedrate == 0 ? 100 : new_filament_e_feedrate;

                config.set_key_value("max_layer_z", new ConfigOptionFloat(gcodegen.m_max_layer_z));
                config.set_key_value("relative_e_axis", new ConfigOptionBool(full_config.use_relative_e_distances));
                config.set_key_value("toolchange_count", new ConfigOptionInt((int) gcodegen.m_toolchange_count));
                // BBS: fan speed is useless placeholer now, but we don't remove it to avoid
                // slicing error in old change_filament_gcode in old 3MF
                config.set_key_value("fan_speed", new ConfigOptionInt((int) 0));
                config.set_key_value("old_retract_length", new ConfigOptionFloat(old_retract_length));
                config.set_key_value("new_retract_length", new ConfigOptionFloat(new_retract_length));
                config.set_key_value("old_retract_length_toolchange", new ConfigOptionFloat(old_retract_length_toolchange));
                config.set_key_value("new_retract_length_toolchange", new ConfigOptionFloat(new_retract_length_toolchange));
                config.set_key_value("old_filament_temp", new ConfigOptionInt(old_filament_temp));
                config.set_key_value("new_filament_temp", new ConfigOptionInt(new_filament_temp));
                config.set_key_value("x_after_toolchange", new ConfigOptionFloat(start_pos(0)));
                config.set_key_value("y_after_toolchange", new ConfigOptionFloat(start_pos(1)));
                config.set_key_value("z_after_toolchange", new ConfigOptionFloat(nozzle_pos(2)));
                config.set_key_value("first_flush_volume", new ConfigOptionFloat(purge_length / 2.f));
                config.set_key_value("second_flush_volume", new ConfigOptionFloat(purge_length / 2.f));
                config.set_key_value("old_filament_e_feedrate", new ConfigOptionInt(old_filament_e_feedrate));
                config.set_key_value("new_filament_e_feedrate", new ConfigOptionInt(new_filament_e_feedrate));
                config.set_key_value("travel_point_1_x", new ConfigOptionFloat(float(travel_point_1.x())));
                config.set_key_value("travel_point_1_y", new ConfigOptionFloat(float(travel_point_1.y())));
                config.set_key_value("travel_point_2_x", new ConfigOptionFloat(float(travel_point_2.x())));
                config.set_key_value("travel_point_2_y", new ConfigOptionFloat(float(travel_point_2.y())));
                config.set_key_value("travel_point_3_x", new ConfigOptionFloat(float(travel_point_3.x())));
                config.set_key_value("travel_point_3_y", new ConfigOptionFloat(float(travel_point_3.y())));

                config.set_key_value("flush_length", new ConfigOptionFloat(purge_length));

                int   flush_count = std::min(g_max_flush_count, (int) std::round(purge_volume / g_purge_volume_one_time));
                float flush_unit  = purge_length / flush_count;
                int   flush_idx   = 0;
                for (; flush_idx < flush_count; flush_idx++) {
                    char key_value[64] = {0};
                    snprintf(key_value, sizeof(key_value), "flush_length_%d", flush_idx + 1);
                    config.set_key_value(key_value, new ConfigOptionFloat(flush_unit));
                }

                for (; flush_idx < g_max_flush_count; flush_idx++) {
                    char key_value[64] = {0};
                    snprintf(key_value, sizeof(key_value), "flush_length_%d", flush_idx + 1);
                    config.set_key_value(key_value, new ConfigOptionFloat(0.f));
                }
            }
            toolchange_gcode_str = gcodegen.placeholder_parser_process("change_filament_gcode", change_filament_gcode, new_extruder_id,
                                                                       &config);
            check_add_eol(toolchange_gcode_str);

            // retract before toolchange
            toolchange_gcode_str = toolchange_retract_str + toolchange_gcode_str;
            // BBS
            {
                // BBS: current position and fan_speed is unclear after interting change_filament_gcode
                check_add_eol(toolchange_gcode_str);
                toolchange_gcode_str += ";_FORCE_RESUME_FAN_SPEED\n";
                gcodegen.writer().set_current_position_clear(false);
                // BBS: check whether custom gcode changes the z position. Update if changed
                double temp_z_after_tool_change;
                if (GCodeProcessor::get_last_z_from_gcode(toolchange_gcode_str, temp_z_after_tool_change)) {
                    Vec3d pos = gcodegen.writer().get_position();
                    pos(2)    = temp_z_after_tool_change;
                    gcodegen.writer().set_position(pos);
                }
            }

            // move to start_pos for wiping after toolchange
            std::string start_pos_str;
            start_pos_str = gcodegen.travel_to(wipe_tower_point_to_object_point(gcodegen, start_pos + plate_origin_2d), erMixed,
                                               "Move to start pos");
            check_add_eol(start_pos_str);
            toolchange_gcode_str += start_pos_str;

            // unretract before wiping
            toolchange_gcode_str += gcodegen.unretract();
            check_add_eol(toolchange_gcode_str);
        }

        std::string toolchange_command;
        if (tcr.priming || (new_extruder_id >= 0 && gcodegen.writer().need_toolchange(new_extruder_id)))
            toolchange_command = gcodegen.writer().toolchange(new_extruder_id);
        if (!custom_gcode_changes_tool(toolchange_gcode_str, gcodegen.writer().toolchange_prefix(), new_extruder_id))
            toolchange_gcode_str += toolchange_command;
        else {
            // We have informed the m_writer about the current extruder_id, we can ignore the generated G-code.
        }

        gcodegen.placeholder_parser().set("current_extruder", new_extruder_id);
        gcodegen.placeholder_parser().set("retraction_distance_when_cut", gcodegen.m_config.retraction_distances_when_cut.get_at(new_extruder_id));
        gcodegen.placeholder_parser().set("long_retraction_when_cut", gcodegen.m_config.long_retractions_when_cut.get_at(new_extruder_id));

        // Process the start filament gcode.
        std::string        start_filament_gcode_str;
        const std::string &filament_start_gcode = gcodegen.config().filament_start_gcode.get_at(new_extruder_id);
        if (!filament_start_gcode.empty()) {
            // Process the filament_start_gcode for the active filament only.
            DynamicConfig config;
            config.set_key_value("filament_extruder_id", new ConfigOptionInt(new_extruder_id));
            start_filament_gcode_str = gcodegen.placeholder_parser_process("filament_start_gcode", filament_start_gcode, new_extruder_id,
                                                                           &config);
            check_add_eol(start_filament_gcode_str);
        }

        // Insert the end filament, toolchange, and start filament gcode into the generated gcode.
        DynamicConfig config;
        config.set_key_value("filament_end_gcode", new ConfigOptionString(end_filament_gcode_str));
        config.set_key_value("change_filament_gcode", new ConfigOptionString(toolchange_gcode_str));
        config.set_key_value("filament_start_gcode", new ConfigOptionString(start_filament_gcode_str));
        std::string tcr_gcode,
            tcr_escaped_gcode = gcodegen.placeholder_parser_process("tcr_rotated_gcode", tcr_rotated_gcode, new_extruder_id, &config);
        unescape_string_cstyle(tcr_escaped_gcode, tcr_gcode);
        gcode += tcr_gcode;
        check_add_eol(toolchange_gcode_str);

        // SoftFever: set new PA for new filament
        if (gcodegen.config().enable_pressure_advance.get_at(new_extruder_id)) {
            gcode += gcodegen.writer().set_pressure_advance(gcodegen.config().pressure_advance.get_at(new_extruder_id));
            // Orca: Adaptive PA
            // Reset Adaptive PA processor last PA value
            gcodegen.m_pa_processor->resetPreviousPA(gcodegen.config().pressure_advance.get_at(new_extruder_id));
        }

        // A phony move to the end position at the wipe tower.
        gcodegen.writer().travel_to_xy((end_pos + plate_origin_2d).cast<double>());
        gcodegen.set_last_pos(wipe_tower_point_to_object_point(gcodegen, end_pos + plate_origin_2d));
        if (!is_approx(z, current_z)) {
            gcode += gcodegen.writer().retract();
            gcode += gcodegen.writer().travel_to_z(current_z, "Travel back up to the topmost object layer.");
            gcode += gcodegen.writer().unretract();
        }

        else {
            // Prepare a future wipe.
            gcodegen.m_wipe.reset_path();
            for (const Vec2f &wipe_pt : tcr.wipe_path)
                gcodegen.m_wipe.path.points.emplace_back(wipe_tower_point_to_object_point(gcodegen, transform_wt_pt(wipe_pt)));
        }

        // Let the planner know we are traveling between objects.
        gcodegen.m_avoid_crossing_perimeters.use_external_mp_once();
        return gcode;
    }

    std::string WipeTowerIntegration::append_tcr2(GCode                             &gcodegen,
                                                  const WipeTower::ToolChangeResult &tcr,
                                                  int                                new_extruder_id,
                                                  double                             z) const
    {
        if (new_extruder_id != -1 && new_extruder_id != tcr.new_tool)
            throw Slic3r::InvalidArgument("Error: WipeTowerIntegration::append_tcr was asked to do a toolchange it didn't expect.");

        std::string gcode;

        // Toolchangeresult.gcode assumes the wipe tower corner is at the origin (except for priming lines)
        // We want to rotate and shift all extrusions (gcode postprocessing) and starting and ending position
        float alpha = m_wipe_tower_rotation / 180.f * float(M_PI);

        auto transform_wt_pt = [&alpha, this](const Vec2f &pt) -> Vec2f {
            Vec2f out = Eigen::Rotation2Df(alpha) * pt;
            out += m_wipe_tower_pos;
            return out;
        };

        Vec2f start_pos = tcr.start_pos;
        Vec2f end_pos   = tcr.end_pos;
        if (!tcr.priming) {
            start_pos = transform_wt_pt(start_pos);
            end_pos   = transform_wt_pt(end_pos);
        }

        Vec2f wipe_tower_offset   = tcr.priming ? Vec2f::Zero() : m_wipe_tower_pos;
        float wipe_tower_rotation = tcr.priming ? 0.f : alpha;
        Vec2f plate_origin_2d(m_plate_origin(0), m_plate_origin(1));


        std::string tcr_rotated_gcode = post_process_wipe_tower_moves(tcr, wipe_tower_offset, wipe_tower_rotation);

        gcode += gcodegen.writer().unlift(); // Make sure there is no z-hop (in most cases, there isn't).

        double current_z = gcodegen.writer().get_position().z();


        if (z == -1.) // in case no specific z was provided, print at current_z pos
            z = current_z;

        const bool needs_toolchange = gcodegen.writer().need_toolchange(new_extruder_id);
        const bool will_go_down     = !is_approx(z, current_z);
        const bool is_ramming       = (gcodegen.config().single_extruder_multi_material) ||
                                (!gcodegen.config().single_extruder_multi_material &&
                                 gcodegen.config().filament_multitool_ramming.get_at(tcr.initial_tool));
        const bool should_travel_to_tower = !tcr.priming && (tcr.force_travel     // wipe tower says so
                                                             || !needs_toolchange // this is just finishing the tower with no toolchange
                                                             || is_ramming);

        if (should_travel_to_tower || gcodegen.m_need_change_layer_lift_z) {
            // FIXME: It would be better if the wipe tower set the force_travel flag for all toolchanges,
            // then we could simplify the condition and make it more readable.
            gcode += gcodegen.retract();
            gcodegen.m_avoid_crossing_perimeters.use_external_mp_once();
            gcode += gcodegen.travel_to(wipe_tower_point_to_object_point(gcodegen, start_pos + plate_origin_2d), erMixed, "Travel to a Wipe Tower");
            gcode += gcodegen.unretract();
        } else {
            // When this is multiextruder printer without any ramming, we can just change
            // the tool without travelling to the tower.
        }

        if (will_go_down) {
            gcode += gcodegen.writer().retract();
            gcode += gcodegen.writer().travel_to_z(z, "Travel down to the last wipe tower layer.");
            gcode += gcodegen.writer().unretract();
        }

        std::string toolchange_gcode_str;
        std::string deretraction_str;
        if (tcr.priming || (new_extruder_id >= 0 && needs_toolchange)) {
            if (is_ramming)
                gcodegen.m_wipe.reset_path();                                           // We don't want wiping on the ramming lines.
            toolchange_gcode_str = gcodegen.set_extruder(new_extruder_id, tcr.print_z); // TODO: toolchange_z vs print_z
            if (gcodegen.config().enable_prime_tower) {
            deretraction_str += gcodegen.writer().travel_to_z(z, "restore layer Z");
                Vec3d position{gcodegen.writer().get_position()};
                position.z() = z;
                gcodegen.writer().set_position(position);
                deretraction_str += gcodegen.unretract();
            }
        }

        // Insert the toolchange and deretraction gcode into the generated gcode.

        DynamicConfig config;
        config.set_key_value("change_filament_gcode", new ConfigOptionString(toolchange_gcode_str));
        config.set_key_value("deretraction_from_wipe_tower_generator", new ConfigOptionString(deretraction_str));
        config.set_key_value("layer_num", new ConfigOptionInt(gcodegen.m_layer_index));
        config.set_key_value("layer_z", new ConfigOptionFloat(tcr.print_z));
        config.set_key_value("toolchange_z", new ConfigOptionFloat(z));

        std::string tcr_gcode,
            tcr_escaped_gcode = gcodegen.placeholder_parser_process("tcr_rotated_gcode", tcr_rotated_gcode, new_extruder_id, &config);
        unescape_string_cstyle(tcr_escaped_gcode, tcr_gcode);
        gcode += tcr_gcode;
        check_add_eol(toolchange_gcode_str);

        // SoftFever: set new PA for new filament
        if (new_extruder_id != -1 && gcodegen.config().enable_pressure_advance.get_at(new_extruder_id)) {
            gcode += gcodegen.writer().set_pressure_advance(gcodegen.config().pressure_advance.get_at(new_extruder_id));
            // Orca: Adaptive PA
            // Reset Adaptive PA processor last PA value
            gcodegen.m_pa_processor->resetPreviousPA(gcodegen.config().pressure_advance.get_at(new_extruder_id));
        }

        // A phony move to the end position at the wipe tower.
        gcodegen.writer().travel_to_xy((end_pos + plate_origin_2d).cast<double>());
        gcodegen.set_last_pos(wipe_tower_point_to_object_point(gcodegen, end_pos + plate_origin_2d));
        if (!is_approx(z, current_z)) {
            gcode += gcodegen.writer().retract();
            gcode += gcodegen.writer().travel_to_z(current_z, "Travel back up to the topmost object layer.");
            gcode += gcodegen.writer().unretract();
        }

        else {
            // Prepare a future wipe.
            gcodegen.m_wipe.reset_path();
            for (const Vec2f &wipe_pt : tcr.wipe_path)
                gcodegen.m_wipe.path.points.emplace_back(wipe_tower_point_to_object_point(gcodegen, transform_wt_pt(wipe_pt)));
        }

        // Let the planner know we are traveling between objects.
        gcodegen.m_avoid_crossing_perimeters.use_external_mp_once();
        return gcode;
    }

    // This function postprocesses gcode_original, rotates and moves all G1 extrusions and returns resulting gcode
    // Starting position has to be supplied explicitely (otherwise it would fail in case first G1 command only contained one coordinate)
    std::string WipeTowerIntegration::post_process_wipe_tower_moves(const WipeTower::ToolChangeResult& tcr, const Vec2f& translation, float angle) const
    {
        Vec2f extruder_offset;
        if (m_single_extruder_multi_material)
            extruder_offset = m_extruder_offsets[0].cast<float>();
        else
            extruder_offset = m_extruder_offsets[tcr.initial_tool].cast<float>();

        std::istringstream gcode_str(tcr.gcode);
        std::string gcode_out;
        std::string line;
        Vec2f pos = tcr.start_pos;
        Vec2f transformed_pos = pos;
        Vec2f old_pos(-1000.1f, -1000.1f);

        while (gcode_str) {
            std::getline(gcode_str, line);  // we read the gcode line by line

            // All G1 commands should be translated and rotated. X and Y coords are
            // only pushed to the output when they differ from last time.
            // WT generator can override this by appending the never_skip_tag
            if (line.find("G1 ") == 0) {
                bool never_skip = false;
                auto it = line.find(WipeTower::never_skip_tag());
                if (it != std::string::npos) {
                    // remove the tag and remember we saw it
                    never_skip = true;
                    line.erase(it, it + WipeTower::never_skip_tag().size());
                }
                std::ostringstream line_out;
                std::istringstream line_str(line);
                line_str >> std::noskipws;  // don't skip whitespace
                char ch = 0;
                while (line_str >> ch) {
                    if (ch == 'X' || ch == 'Y')
                        line_str >> (ch == 'X' ? pos.x() : pos.y());
                    else
                        line_out << ch;
                }

                transformed_pos = Eigen::Rotation2Df(angle) * pos + translation;

                if (transformed_pos != old_pos || never_skip) {
                    line = line_out.str();
                    std::ostringstream oss;
                    oss << std::fixed << std::setprecision(3) << "G1 ";
                    if (transformed_pos.x() != old_pos.x() || never_skip)
                        oss << " X" << transformed_pos.x() - extruder_offset.x();
                    if (transformed_pos.y() != old_pos.y() || never_skip)
                        oss << " Y" << transformed_pos.y() - extruder_offset.y();
                    oss << " ";
                    line.replace(line.find("G1 "), 3, oss.str());
                    old_pos = transformed_pos;
                }
            }

            gcode_out += line + "\n";

            // If this was a toolchange command, we should change current extruder offset
            if (line == "[change_filament_gcode]") {
                // BBS
                if (!m_single_extruder_multi_material) {
                    extruder_offset = m_extruder_offsets[tcr.new_tool].cast<float>();

                    // If the extruder offset changed, add an extra move so everything is continuous
                    if (extruder_offset != m_extruder_offsets[tcr.initial_tool].cast<float>()) {
                        std::ostringstream oss;
                        oss << std::fixed << std::setprecision(3)
                            << "G1 X" << transformed_pos.x() - extruder_offset.x()
                            << " Y" << transformed_pos.y() - extruder_offset.y()
                            << "\n";
                        gcode_out += oss.str();
                    }
                }
            }
        }
        return gcode_out;
    }

    std::string WipeTowerIntegration::prime(GCode &gcodegen)
    {
        std::string gcode;
        if (!gcodegen.is_BBL_Printer()) {
            for (const WipeTower::ToolChangeResult &tcr : m_priming) {
                if (!tcr.extrusions.empty())
                    gcode += append_tcr2(gcodegen, tcr, tcr.new_tool);
            }
        }
        return gcode;
    }

    std::string WipeTowerIntegration::tool_change(GCode &gcodegen, int extruder_id, bool finish_layer)
    {
        std::string gcode;

        assert(m_layer_idx >= 0);
        if (m_layer_idx >= (int) m_tool_changes.size())
            return gcode;
        if (!gcodegen.is_BBL_Printer()) {
            if (gcodegen.writer().need_toolchange(extruder_id) || finish_layer) {
                if (m_layer_idx < (int) m_tool_changes.size()) {
                    if (!(size_t(m_tool_change_idx) < m_tool_changes[m_layer_idx].size()))
                        throw Slic3r::RuntimeError("Wipe tower generation failed, possibly due to empty first layer.");

                    // Calculate where the wipe tower layer will be printed. -1 means that print z will not change,
                    // resulting in a wipe tower with sparse layers.
                    double wipe_tower_z  = -1;
                    bool   ignore_sparse = false;
                    if (gcodegen.config().wipe_tower_no_sparse_layers.value) {
                        wipe_tower_z  = m_last_wipe_tower_print_z;
                        ignore_sparse = (m_tool_changes[m_layer_idx].size() == 1 &&
                                         m_tool_changes[m_layer_idx].front().initial_tool == m_tool_changes[m_layer_idx].front().new_tool &&
                                         m_layer_idx != 0);
                        if (m_tool_change_idx == 0 && !ignore_sparse)
                        wipe_tower_z = m_last_wipe_tower_print_z + m_tool_changes[m_layer_idx].front().layer_height;
                    }

                    if (!ignore_sparse) {
                        gcode += append_tcr2(gcodegen, m_tool_changes[m_layer_idx][m_tool_change_idx++], extruder_id, wipe_tower_z);
                        m_last_wipe_tower_print_z = wipe_tower_z;
                    }
                }
            }
        } else {
            // Calculate where the wipe tower layer will be printed. -1 means that print z will not change,
            // resulting in a wipe tower with sparse layers.
            double wipe_tower_z  = -1;
            bool   ignore_sparse = false;
            if (gcodegen.config().wipe_tower_no_sparse_layers.value) {
                wipe_tower_z  = m_last_wipe_tower_print_z;
                ignore_sparse = (m_tool_changes[m_layer_idx].size() == 1 &&
                                 m_tool_changes[m_layer_idx].front().initial_tool == m_tool_changes[m_layer_idx].front().new_tool);
                if (m_tool_change_idx == 0 && !ignore_sparse)
                    wipe_tower_z = m_last_wipe_tower_print_z + m_tool_changes[m_layer_idx].front().layer_height;
            }

            if (m_enable_timelapse_print && m_is_first_print) {
                gcode += append_tcr(gcodegen, m_tool_changes[m_layer_idx][0], m_tool_changes[m_layer_idx][0].new_tool, wipe_tower_z);
                m_tool_change_idx++;
                m_is_first_print = false;
            }

            if (gcodegen.writer().need_toolchange(extruder_id) || finish_layer) {
                if (!(size_t(m_tool_change_idx) < m_tool_changes[m_layer_idx].size()))
                    throw Slic3r::RuntimeError("Wipe tower generation failed, possibly due to empty first layer.");

                if (!ignore_sparse) {
                    gcode += append_tcr(gcodegen, m_tool_changes[m_layer_idx][m_tool_change_idx++], extruder_id, wipe_tower_z);
                    m_last_wipe_tower_print_z = wipe_tower_z;
                }
            }
        }

        return gcode;
    }

    bool WipeTowerIntegration::is_empty_wipe_tower_gcode(GCode &gcodegen, int extruder_id, bool finish_layer)
    {
        assert(m_layer_idx >= 0);
        if (m_layer_idx >= (int) m_tool_changes.size())
            return true;

        bool   ignore_sparse = false;
        if (gcodegen.config().wipe_tower_no_sparse_layers.value) {
            ignore_sparse = (m_tool_changes[m_layer_idx].size() == 1 && m_tool_changes[m_layer_idx].front().initial_tool == m_tool_changes[m_layer_idx].front().new_tool);
        }

        if (m_enable_timelapse_print && m_is_first_print) {
            return false;
        }

        if (gcodegen.writer().need_toolchange(extruder_id) || finish_layer) {
            if (!(size_t(m_tool_change_idx) < m_tool_changes[m_layer_idx].size()))
                throw Slic3r::RuntimeError("Wipe tower generation failed, possibly due to empty first layer.");

            if (!ignore_sparse) {
                return false;
            }
        }

        return true;
    }

    // Print is finished. Now it remains to unload the filament safely with ramming over the wipe tower.
    std::string WipeTowerIntegration::finalize(GCode &gcodegen)
    {
        std::string gcode;
        if (!gcodegen.is_BBL_Printer()) {
            if (std::abs(gcodegen.writer().get_position().z() - m_final_purge.print_z) > EPSILON)
                gcode += gcodegen.change_layer(m_final_purge.print_z);
            gcode += append_tcr2(gcodegen, m_final_purge, -1);
        }

        return gcode;
    }

    const std::vector<std::string> ColorPrintColors::Colors = { "#C0392B", "#E67E22", "#F1C40F", "#27AE60", "#1ABC9C", "#2980B9", "#9B59B6" };

#define EXTRUDER_CONFIG(OPT) m_config.OPT.get_at(m_writer.extruder()->id())

void GCode::PlaceholderParserIntegration::reset()
{
    this->failed_templates.clear();
    this->output_config.clear();
    this->opt_position = nullptr;
    this->opt_zhop      = nullptr;
    this->opt_e_position = nullptr;
    this->opt_e_retracted = nullptr;
    this->opt_e_restart_extra = nullptr;
    this->opt_extruded_volume = nullptr;
    this->opt_extruded_weight = nullptr;
    this->opt_extruded_volume_total = nullptr;
    this->opt_extruded_weight_total = nullptr;
    this->num_extruders = 0;
    this->position.clear();
    this->e_position.clear();
    this->e_retracted.clear();
    this->e_restart_extra.clear();
}

void GCode::PlaceholderParserIntegration::init(const GCodeWriter &writer)
{
    this->reset();
    const std::vector<Extruder> &extruders = writer.extruders();
    if (! extruders.empty()) {
        this->num_extruders = extruders.back().id() + 1;
        this->e_retracted.assign(MAXIMUM_EXTRUDER_NUMBER, 0);
        this->e_restart_extra.assign(MAXIMUM_EXTRUDER_NUMBER, 0);
        this->opt_e_retracted = new ConfigOptionFloats(e_retracted);
        this->opt_e_restart_extra = new ConfigOptionFloats(e_restart_extra);
        this->output_config.set_key_value("e_retracted", this->opt_e_retracted);
        this->output_config.set_key_value("e_restart_extra", this->opt_e_restart_extra);
        if (! writer.config.use_relative_e_distances) {
            e_position.assign(MAXIMUM_EXTRUDER_NUMBER, 0);
            opt_e_position = new ConfigOptionFloats(e_position);
            this->output_config.set_key_value("e_position", opt_e_position);
        }
    }
    this->opt_extruded_volume = new ConfigOptionFloats(this->num_extruders, 0.f);
    this->opt_extruded_weight = new ConfigOptionFloats(this->num_extruders, 0.f);
    this->opt_extruded_volume_total = new ConfigOptionFloat(0.f);
    this->opt_extruded_weight_total = new ConfigOptionFloat(0.f);
    this->parser.set("extruded_volume", this->opt_extruded_volume);
    this->parser.set("extruded_weight", this->opt_extruded_weight);
    this->parser.set("extruded_volume_total", this->opt_extruded_volume_total);
    this->parser.set("extruded_weight_total", this->opt_extruded_weight_total);

    // Reserve buffer for current position.
    this->position.assign(3, 0);
    this->opt_position = new ConfigOptionFloats(this->position);
    this->output_config.set_key_value("position", this->opt_position);
    // Store zhop variable into the parser itself, it is a read-only variable to the script.
    this->opt_zhop = new ConfigOptionFloat(writer.get_zhop());
    this->parser.set("zhop", this->opt_zhop);
}

void GCode::PlaceholderParserIntegration::update_from_gcodewriter(const GCodeWriter &writer)
{
    memcpy(this->position.data(), writer.get_position().data(), sizeof(double) * 3);
    this->opt_position->values = this->position;
    this->opt_zhop->value = writer.get_zhop();

    if (this->num_extruders > 0) {
        const std::vector<Extruder> &extruders = writer.extruders();
        assert(! extruders.empty() && num_extruders == extruders.back().id() + 1);
        this->e_retracted.assign(MAXIMUM_EXTRUDER_NUMBER, 0);
        this->e_restart_extra.assign(MAXIMUM_EXTRUDER_NUMBER, 0);
        this->opt_extruded_volume->values.assign(num_extruders, 0);
        this->opt_extruded_weight->values.assign(num_extruders, 0);
        double total_volume = 0.;
        double total_weight = 0.;
        for (const Extruder &e : extruders) {
            this->e_retracted[e.id()]     = e.retracted();
            this->e_restart_extra[e.id()] = e.restart_extra();
            double v = e.extruded_volume();
            double w = v * e.filament_density() * 0.001;
            this->opt_extruded_volume->values[e.id()] = v;
            this->opt_extruded_weight->values[e.id()] = w;
            total_volume += v;
            total_weight += w;
        }
        opt_extruded_volume_total->value = total_volume;
        opt_extruded_weight_total->value = total_weight;
        opt_e_retracted->values = this->e_retracted;
        opt_e_restart_extra->values = this->e_restart_extra;
        if (! writer.config.use_relative_e_distances) {
            this->e_position.assign(MAXIMUM_EXTRUDER_NUMBER, 0);
            for (const Extruder &e : extruders)
                this->e_position[e.id()] = e.position();
            this->opt_e_position->values = this->e_position;
        }
    }
}

// Throw if any of the output vector variables were resized by the script.
void GCode::PlaceholderParserIntegration::validate_output_vector_variables()
{
    if (this->opt_position->values.size() != 3)
        throw Slic3r::RuntimeError("\"position\" output variable must not be resized by the script.");
    if (this->num_extruders > 0) {
        if (this->opt_e_position && this->opt_e_position->values.size() != MAXIMUM_EXTRUDER_NUMBER)
            throw Slic3r::RuntimeError("\"e_position\" output variable must not be resized by the script.");
        if (this->opt_e_retracted->values.size() != MAXIMUM_EXTRUDER_NUMBER)
            throw Slic3r::RuntimeError("\"e_retracted\" output variable must not be resized by the script.");
        if (this->opt_e_restart_extra->values.size() != MAXIMUM_EXTRUDER_NUMBER)
            throw Slic3r::RuntimeError("\"e_restart_extra\" output variable must not be resized by the script.");
    }
}

// Collect pairs of object_layer + support_layer sorted by print_z.
// object_layer & support_layer are considered to be on the same print_z, if they are not further than EPSILON.
std::vector<GCode::LayerToPrint> GCode::collect_layers_to_print(const PrintObject& object)
{
    std::vector<GCode::LayerToPrint> layers_to_print;
    layers_to_print.reserve(object.layers().size() + object.support_layers().size());

    /*
    // Calculate a minimum support layer height as a minimum over all extruders, but not smaller than 10um.
    // This is the same logic as in support generator.
    //FIXME should we use the printing extruders instead?
    double gap_over_supports = object.config().support_top_z_distance;
    // FIXME should we test object.config().support_material_synchronize_layers ? Currently the support layers are synchronized with object layers iff soluble supports.
    assert(!object.has_support() || gap_over_supports != 0. || object.config().support_material_synchronize_layers);
    if (gap_over_supports != 0.) {
        gap_over_supports = std::max(0., gap_over_supports);
        // Not a soluble support,
        double support_layer_height_min = 1000000.;
        for (auto lh : object.print()->config().min_layer_height.values)
            support_layer_height_min = std::min(support_layer_height_min, std::max(0.01, lh));
        gap_over_supports += support_layer_height_min;
    }*/

    std::vector<std::pair<double, double>> warning_ranges;

    // Pair the object layers with the support layers by z.
    size_t idx_object_layer = 0;
    size_t idx_support_layer = 0;
    const LayerToPrint* last_extrusion_layer = nullptr;
    while (idx_object_layer < object.layers().size() || idx_support_layer < object.support_layers().size()) {
        LayerToPrint layer_to_print;
        double print_z_min = std::numeric_limits<double>::max();
        if (idx_object_layer < object.layers().size()) {
            layer_to_print.object_layer = object.layers()[idx_object_layer++];
            print_z_min = std::min(print_z_min, layer_to_print.object_layer->print_z);
        }

        if (idx_support_layer < object.support_layers().size()) {
            layer_to_print.support_layer = object.support_layers()[idx_support_layer++];
            print_z_min = std::min(print_z_min, layer_to_print.support_layer->print_z);
        }

        if (layer_to_print.object_layer && layer_to_print.object_layer->print_z > print_z_min + EPSILON) {
            layer_to_print.object_layer = nullptr;
            --idx_object_layer;
        }

        if (layer_to_print.support_layer && layer_to_print.support_layer->print_z > print_z_min + EPSILON) {
            layer_to_print.support_layer = nullptr;
            --idx_support_layer;
        }

        layer_to_print.original_object = &object;
        layers_to_print.push_back(layer_to_print);

        bool has_extrusions = (layer_to_print.object_layer && layer_to_print.object_layer->has_extrusions())
            || (layer_to_print.support_layer && layer_to_print.support_layer->has_extrusions());

        // Check that there are extrusions on the very first layer. The case with empty
        // first layer may result in skirt/brim in the air and maybe other issues.
        if (layers_to_print.size() == 1u) {
            if (!has_extrusions)
                throw Slic3r::SlicingError(_(L("One object has empty initial layer and can't be printed. Please Cut the bottom or enable supports.")), object.id().id);
        }

        // In case there are extrusions on this layer, check there is a layer to lay it on.
        if ((layer_to_print.object_layer && layer_to_print.object_layer->has_extrusions())
            // Allow empty support layers, as the support generator may produce no extrusions for non-empty support regions.
            || (layer_to_print.support_layer /* && layer_to_print.support_layer->has_extrusions() */)) {
            double top_cd = object.config().support_top_z_distance;
            double bottom_cd = object.config().support_bottom_z_distance;

            double extra_gap = (layer_to_print.support_layer ? bottom_cd : top_cd);

            // raft contact distance should not trigger any warning
            if(last_extrusion_layer && last_extrusion_layer->support_layer)
                extra_gap = std::max(extra_gap, object.config().raft_contact_distance.value);

            double maximal_print_z = (last_extrusion_layer ? last_extrusion_layer->print_z() : 0.)
                + layer_to_print.layer()->height
                + std::max(0., extra_gap);
            // Negative support_contact_z is not taken into account, it can result in false positives in cases

            if (has_extrusions && layer_to_print.print_z() > maximal_print_z + 2. * EPSILON)
                warning_ranges.emplace_back(std::make_pair((last_extrusion_layer ? last_extrusion_layer->print_z() : 0.), layers_to_print.back().print_z()));
        }
        // Remember last layer with extrusions.
        if (has_extrusions)
            last_extrusion_layer = &layers_to_print.back();
    }

    if (! warning_ranges.empty()) {
        std::string warning;
        size_t i = 0;
        for (i = 0; i < std::min(warning_ranges.size(), size_t(5)); ++i)
            warning += Slic3r::format(_(L("Object can't be printed for empty layer between %1% and %2%.")),
                                      warning_ranges[i].first, warning_ranges[i].second) + "\n";
        warning += Slic3r::format(_(L("Object: %1%")), object.model_object()->name) + "\n"
            + _(L("Maybe parts of the object at these height are too thin, or the object has faulty mesh"));

        const_cast<Print*>(object.print())->active_step_add_warning(
            PrintStateBase::WarningLevel::CRITICAL, warning, PrintStateBase::SlicingEmptyGcodeLayers);
    }

    return layers_to_print;
}

// Prepare for non-sequential printing of multiple objects: Support resp. object layers with nearly identical print_z
// will be printed for  all objects at once.
// Return a list of <print_z, per object LayerToPrint> items.
std::vector<std::pair<coordf_t, std::vector<GCode::LayerToPrint>>> GCode::collect_layers_to_print(const Print& print)
{
    struct OrderingItem {
        coordf_t    print_z;
        size_t      object_idx;
        size_t      layer_idx;
    };

    std::vector<std::vector<LayerToPrint>>  per_object(print.objects().size(), std::vector<LayerToPrint>());
    std::vector<OrderingItem>               ordering;

    std::vector<Slic3r::SlicingError> errors;

    for (size_t i = 0; i < print.objects().size(); ++i) {
        try {
            per_object[i] = collect_layers_to_print(*print.objects()[i]);
        } catch (const Slic3r::SlicingError &e) {
            errors.push_back(e);
            continue;
        }
        OrderingItem ordering_item;
        ordering_item.object_idx = i;
        ordering.reserve(ordering.size() + per_object[i].size());
        const LayerToPrint& front = per_object[i].front();
        for (const LayerToPrint& ltp : per_object[i]) {
            ordering_item.print_z = ltp.print_z();
            ordering_item.layer_idx = &ltp - &front;
            ordering.emplace_back(ordering_item);
        }
    }

    if (!errors.empty()) { throw Slic3r::SlicingErrors(errors); }

    std::sort(ordering.begin(), ordering.end(), [](const OrderingItem& oi1, const OrderingItem& oi2) { return oi1.print_z < oi2.print_z; });

    std::vector<std::pair<coordf_t, std::vector<LayerToPrint>>> layers_to_print;

    // Merge numerically very close Z values.
    for (size_t i = 0; i < ordering.size();) {
        // Find the last layer with roughly the same print_z.
        size_t j = i + 1;
        coordf_t zmax = ordering[i].print_z + EPSILON;
        for (; j < ordering.size() && ordering[j].print_z <= zmax; ++j);
        // Merge into layers_to_print.
        std::pair<coordf_t, std::vector<LayerToPrint>> merged;
        // Assign an average print_z to the set of layers with nearly equal print_z.
        merged.first = 0.5 * (ordering[i].print_z + ordering[j - 1].print_z);
        merged.second.assign(print.objects().size(), LayerToPrint());
        for (; i < j; ++i) {
            const OrderingItem& oi = ordering[i];
            assert(merged.second[oi.object_idx].layer() == nullptr);
            merged.second[oi.object_idx] = std::move(per_object[oi.object_idx][oi.layer_idx]);
        }
        layers_to_print.emplace_back(std::move(merged));
    }

    return layers_to_print;
}

// free functions called by GCode::do_export()
namespace DoExport {
//    static void update_print_estimated_times_stats(const GCodeProcessor& processor, PrintStatistics& print_statistics)
//    {
//        const GCodeProcessorResult& result = processor.get_result();
//        print_statistics.estimated_normal_print_time = get_time_dhms(result.print_statistics.modes[static_cast<size_t>(PrintEstimatedStatistics::ETimeMode::Normal)].time);
//        print_statistics.estimated_silent_print_time = processor.is_stealth_time_estimator_enabled() ?
//            get_time_dhms(result.print_statistics.modes[static_cast<size_t>(PrintEstimatedStatistics::ETimeMode::Stealth)].time) : "N/A";
//    }

    static void update_print_estimated_stats(const GCodeProcessor& processor, const std::vector<Extruder>& extruders, PrintStatistics& print_statistics, const PrintConfig& config)
    {
        const GCodeProcessorResult& result = processor.get_result();
        double normal_print_time = result.print_statistics.modes[static_cast<size_t>(PrintEstimatedStatistics::ETimeMode::Normal)].time;
        print_statistics.estimated_normal_print_time = get_time_dhms(normal_print_time);
        print_statistics.estimated_silent_print_time = processor.is_stealth_time_estimator_enabled() ?
            get_time_dhms(result.print_statistics.modes[static_cast<size_t>(PrintEstimatedStatistics::ETimeMode::Stealth)].time) : "N/A";

        // update filament statictics
        double total_extruded_volume = 0.0;
        double total_used_filament   = 0.0;
        double total_weight          = 0.0;
        double total_cost            = 0.0;

        for (auto volume : result.print_statistics.total_volumes_per_extruder) {
            total_extruded_volume += volume.second;

            size_t extruder_id = volume.first;
            auto extruder = std::find_if(extruders.begin(), extruders.end(), [extruder_id](const Extruder& extr) {return extr.id() == extruder_id; });
            if (extruder == extruders.end())
                continue;

            double s = PI * sqr(0.5* extruder->filament_diameter());
            double weight = volume.second * extruder->filament_density() * 0.001;
            total_used_filament += volume.second/s;
            total_weight        += weight;
            total_cost          += weight * extruder->filament_cost() * 0.001;
        }

        total_cost += config.time_cost.getFloat() * (normal_print_time/3600.0);

        print_statistics.total_extruded_volume = total_extruded_volume;
        print_statistics.total_used_filament   = total_used_filament;
        print_statistics.total_weight          = total_weight;
        print_statistics.total_cost            = total_cost;

        print_statistics.filament_stats = result.print_statistics.model_volumes_per_extruder;
    }

    // if any reserved keyword is found, returns a std::vector containing the first MAX_COUNT keywords found
    // into pairs containing:
    // first: source
    // second: keyword
    // to be shown in the warning notification
    // The returned vector is empty if no keyword has been found
    static std::vector<std::pair<std::string, std::string>> validate_custom_gcode(const Print& print) {
        static const unsigned int MAX_TAGS_COUNT = 5;
        std::vector<std::pair<std::string, std::string>> ret;

        auto check = [&ret](const std::string& source, const std::string& gcode) {
            std::vector<std::string> tags;
            if (GCodeProcessor::contains_reserved_tags(gcode, MAX_TAGS_COUNT, tags)) {
                if (!tags.empty()) {
                    size_t i = 0;
                    while (ret.size() < MAX_TAGS_COUNT && i < tags.size()) {
                        ret.push_back({ source, tags[i] });
                        ++i;
                    }
                }
            }
        };

        const GCodeConfig& config = print.config();
        check(_(L("Machine start G-code")), config.machine_start_gcode.value);
        if (ret.size() < MAX_TAGS_COUNT) check(_(L("Machine end G-code")), config.machine_end_gcode.value);
        if (ret.size() < MAX_TAGS_COUNT) check(_(L("Before layer change G-code")), config.before_layer_change_gcode.value);
        if (ret.size() < MAX_TAGS_COUNT) check(_(L("Layer change G-code")), config.layer_change_gcode.value);
        if (ret.size() < MAX_TAGS_COUNT) check(_(L("Time lapse G-code")), config.time_lapse_gcode.value);
        if (ret.size() < MAX_TAGS_COUNT) check(_(L("Change filament G-code")), config.change_filament_gcode.value);
        if (ret.size() < MAX_TAGS_COUNT) check(_(L("Printing by object G-code")), config.printing_by_object_gcode.value);
        //if (ret.size() < MAX_TAGS_COUNT) check(_(L("Color Change G-code")), config.color_change_gcode.value);
        //Orca
        if (ret.size() < MAX_TAGS_COUNT) check(_(L("Change extrusion role G-code")), config.change_extrusion_role_gcode.value);
        if (ret.size() < MAX_TAGS_COUNT) check(_(L("Pause G-code")), config.machine_pause_gcode.value);
        if (ret.size() < MAX_TAGS_COUNT) check(_(L("Template Custom G-code")), config.template_custom_gcode.value);
        if (ret.size() < MAX_TAGS_COUNT) {
            for (const std::string& value : config.filament_start_gcode.values) {
                check(_(L("Filament start G-code")), value);
                if (ret.size() == MAX_TAGS_COUNT)
                    break;
            }
        }
        if (ret.size() < MAX_TAGS_COUNT) {
            for (const std::string& value : config.filament_end_gcode.values) {
                check(_(L("Filament end G-code")), value);
                if (ret.size() == MAX_TAGS_COUNT)
                    break;
            }
        }
        //BBS: no custom_gcode_per_print_z, don't need to check
        //if (ret.size() < MAX_TAGS_COUNT) {
        //    const CustomGCode::Info& custom_gcode_per_print_z = print.model().custom_gcode_per_print_z;
        //    for (const auto& gcode : custom_gcode_per_print_z.gcodes) {
        //        check(_(L("Custom G-code")), gcode.extra);
        //        if (ret.size() == MAX_TAGS_COUNT)
        //            break;
        //    }
        //}

        return ret;
    }
} // namespace DoExport

bool GCode::is_BBL_Printer()
{
    if (m_curr_print)
        return m_curr_print->is_BBL_printer();
    return false;
}

void GCode::do_export(Print* print, const char* path, GCodeProcessorResult* result, ThumbnailsGeneratorCallback thumbnail_cb)
{
    PROFILE_CLEAR();

    // BBS
    m_curr_print = print;

    GCodeWriter::full_gcode_comment = print->config().gcode_comments;
    CNumericLocalesSetter locales_setter;

    // Does the file exist? If so, we hope that it is still valid.
    if (print->is_step_done(psGCodeExport) && boost::filesystem::exists(boost::filesystem::path(path)))
        return;

    BOOST_LOG_TRIVIAL(info) << boost::format("Will export G-code to %1% soon")%path;
    GCodeProcessor::s_IsBBLPrinter = print->is_BBL_printer();
    print->set_started(psGCodeExport);

    // check if any custom gcode contains keywords used by the gcode processor to
    // produce time estimation and gcode toolpaths
    std::vector<std::pair<std::string, std::string>> validation_res = DoExport::validate_custom_gcode(*print);
    if (!validation_res.empty()) {
        std::string reports;
        for (const auto& [source, keyword] : validation_res) {
            reports += source + ": \"" + keyword + "\"\n";
        }
        //print->active_step_add_warning(PrintStateBase::WarningLevel::NON_CRITICAL,
        //    _(L("In the custom G-code were found reserved keywords:")) + "\n" +
        //    reports +
        //    _(L("This may cause problems in g-code visualization and printing time estimation.")));
        std::string temp = "Dangerous keywords in custom Gcode: " + reports + "\nThis may cause problems in g-code visualization and printing time estimation.";
        BOOST_LOG_TRIVIAL(warning) << temp;
    }

    BOOST_LOG_TRIVIAL(info) << "Exporting G-code..." << log_memory_info();

    // Remove the old g-code if it exists.
    boost::nowide::remove(path);

    fs::path file_path(path);
    fs::path folder = file_path.parent_path();
    if (!fs::exists(folder)) {
        fs::create_directory(folder);
        BOOST_LOG_TRIVIAL(error) << "[WARNING]: the parent path " + folder.string() +" is not there, create it!" << std::endl;
    }

    std::string path_tmp(path);
    path_tmp += ".tmp";

    m_processor.initialize(path_tmp);
    m_processor.set_print(print);
    GCodeOutputStream file(boost::nowide::fopen(path_tmp.c_str(), "wb"), m_processor);
    if (! file.is_open()) {
        BOOST_LOG_TRIVIAL(error) << std::string("G-code export to ") + path + " failed.\nCannot open the file for writing.\n" << std::endl;
        if (!fs::exists(folder)) {
            //fs::create_directory(folder);
            BOOST_LOG_TRIVIAL(error) << "the parent path " + folder.string() +" is not there!!!" << std::endl;
        }
        throw Slic3r::RuntimeError(std::string("G-code export to ") + path + " failed.\nCannot open the file for writing.\n");
    }

    try {
        this->_do_export(*print, file, thumbnail_cb);
        file.flush();
        if (file.is_error()) {
            file.close();
            boost::nowide::remove(path_tmp.c_str());
            throw Slic3r::RuntimeError(std::string("G-code export to ") + path + " failed\nIs the disk full?\n");
        }
    } catch (std::exception & /* ex */) {
        // Rethrow on any exception. std::runtime_exception and CanceledException are expected to be thrown.
        // Close and remove the file.
        file.close();
        boost::nowide::remove(path_tmp.c_str());
        throw;
    }
    file.close();

    check_placeholder_parser_failed();

#if ORCA_CHECK_GCODE_PLACEHOLDERS
    if (!m_placeholder_error_messages.empty()){
        std::ostringstream message;
        message << "Some EditGcodeDialog defs were not specified properly. Do so in PrintConfig under SlicingStatesConfigDef:" << std::endl;
        for (const auto& error : m_placeholder_error_messages) {
            message << std::endl << error.first << ": " << std::endl;
            for (const auto& str : error.second)
                message << str << ", ";
            message.seekp(-2, std::ios_base::end);
            message << std::endl;
        }
        throw Slic3r::PlaceholderParserError(message.str());
    }
#endif

    BOOST_LOG_TRIVIAL(debug) << "Start processing gcode, " << log_memory_info();
    // Post-process the G-code to update time stamps.

    m_timelapse_warning_code = 0;
    if (m_config.printer_structure.value == PrinterStructure::psI3 && m_spiral_vase) {
        m_timelapse_warning_code += 1;
    }
    if (m_config.printer_structure.value == PrinterStructure::psI3 && print->config().print_sequence == PrintSequence::ByObject) {
        m_timelapse_warning_code += (1 << 1);
    }
    m_processor.result().timelapse_warning_code = m_timelapse_warning_code;
    m_processor.result().support_traditional_timelapse = m_support_traditional_timelapse;

    bool activate_long_retraction_when_cut = false;
    for (const auto& extruder : m_writer.extruders())
        activate_long_retraction_when_cut |= (
            m_config.long_retractions_when_cut.get_at(extruder.id()) 
         && m_config.retraction_distances_when_cut.get_at(extruder.id()) > 0
            );

    m_processor.result().long_retraction_when_cut = activate_long_retraction_when_cut;
   
    {   //BBS:check bed and filament compatible
        const ConfigOptionDef *bed_type_def = print_config_def.get("curr_bed_type");
        assert(bed_type_def != nullptr);
        const t_config_enum_values *bed_type_keys_map = bed_type_def->enum_keys_map;
        const ConfigOptionInts *bed_temp_opt = m_config.option<ConfigOptionInts>(get_bed_temp_key(m_config.curr_bed_type));
        for(auto extruder_id : m_initial_layer_extruders){
            int cur_bed_temp = bed_temp_opt->get_at(extruder_id);
            if (cur_bed_temp == 0 && bed_type_keys_map != nullptr) {
                for (auto item : *bed_type_keys_map) {
                    if (item.second == m_config.curr_bed_type) {
                        m_processor.result().bed_match_result = BedMatchResult(false, item.first, extruder_id);
                        break;
                    }
                }
            }
            if (m_processor.result().bed_match_result.match == false)
                break;
        }
    }

    m_processor.finalize(true);
//    DoExport::update_print_estimated_times_stats(m_processor, print->m_print_statistics);
    DoExport::update_print_estimated_stats(m_processor, m_writer.extruders(), print->m_print_statistics, print->config());
    if (result != nullptr) {
        *result = std::move(m_processor.extract_result());
        // set the filename to the correct value
        result->filename = path;
    }

    //BBS: add some log for error output
    BOOST_LOG_TRIVIAL(debug) << boost::format("Finished processing gcode to %1% ") % path_tmp;

    std::error_code ret = rename_file(path_tmp, path);
    if (ret) {
        throw Slic3r::RuntimeError(
            std::string("Failed to rename the output G-code file from ") + path_tmp + " to " + path + '\n' + "error code " + ret.message() + '\n' +
            "Is " + path_tmp + " locked?" + '\n');
    }
    else {
        BOOST_LOG_TRIVIAL(info) << boost::format("rename_file from %1% to %2% successfully")% path_tmp % path;
    }

    BOOST_LOG_TRIVIAL(info) << "Exporting G-code finished" << log_memory_info();
    print->set_done(psGCodeExport);
    
    if(is_BBL_Printer())
        result->label_object_enabled = m_enable_exclude_object;

    // Write the profiler measurements to file
    PROFILE_UPDATE();
    PROFILE_OUTPUT(debug_out_path("gcode-export-profile.txt").c_str());
}

// free functions called by GCode::_do_export()
namespace DoExport {
    static void init_gcode_processor(const PrintConfig& config, GCodeProcessor& processor, bool& silent_time_estimator_enabled)
    {
        silent_time_estimator_enabled = (config.gcode_flavor == gcfMarlinLegacy || config.gcode_flavor == gcfMarlinFirmware)
                                        && config.silent_mode;
        processor.reset();
        processor.apply_config(config);
        processor.enable_stealth_time_estimator(silent_time_estimator_enabled);
    }

#if 0
	static double autospeed_volumetric_limit(const Print &print)
	{
	    // get the minimum cross-section used in the print
	    std::vector<double> mm3_per_mm;
	    for (auto object : print.objects()) {
	        for (size_t region_id = 0; region_id < object->num_printing_regions(); ++ region_id) {
	            const PrintRegion &region = object->printing_region(region_id);
	            for (auto layer : object->layers()) {
	                const LayerRegion* layerm = layer->regions()[region_id];
	                if (region.config().get_abs_value("inner_wall_speed") == 0 ||
                        // BBS: remove small small_perimeter_speed config, and will absolutely
                        // remove related code if no other issue in the coming release.
	                    //region.config().get_abs_value("small_perimeter_speed") == 0 ||
	                    region.config().outer_wall_speed.value == 0 ||
	                    region.config().get_abs_value("bridge_speed") == 0)
	                    mm3_per_mm.push_back(layerm->perimeters.min_mm3_per_mm());
	                if (region.config().get_abs_value("sparse_infill_speed") == 0 ||
	                    region.config().get_abs_value("internal_solid_infill_speed") == 0 ||
	                    region.config().get_abs_value("top_surface_speed") == 0 ||
                        region.config().get_abs_value("bridge_speed") == 0)
                    {
                        // Minimal volumetric flow should not be calculated over ironing extrusions.
                        // Use following lambda instead of the built-it method.
                        auto min_mm3_per_mm_no_ironing = [](const ExtrusionEntityCollection& eec) -> double {
                            double min = std::numeric_limits<double>::max();
                            for (const ExtrusionEntity* ee : eec.entities)
                                if (ee->role() != erIroning)
                                    min = std::min(min, ee->min_mm3_per_mm());
                            return min;
                        };

                        mm3_per_mm.push_back(min_mm3_per_mm_no_ironing(layerm->fills));
                    }
	            }
	        }
	        if (object->config().get_abs_value("support_speed") == 0 ||
	            object->config().get_abs_value("support_interface_speed") == 0)
	            for (auto layer : object->support_layers())
	                mm3_per_mm.push_back(layer->support_fills.min_mm3_per_mm());
	    }
	    // filter out 0-width segments
	    mm3_per_mm.erase(std::remove_if(mm3_per_mm.begin(), mm3_per_mm.end(), [](double v) { return v < 0.000001; }), mm3_per_mm.end());
	    double volumetric_speed = 0.;
	    if (! mm3_per_mm.empty()) {
	        // In order to honor max_print_speed we need to find a target volumetric
	        // speed that we can use throughout the print. So we define this target
	        // volumetric speed as the volumetric speed produced by printing the
	        // smallest cross-section at the maximum speed: any larger cross-section
	        // will need slower feedrates.
	        volumetric_speed = *std::min_element(mm3_per_mm.begin(), mm3_per_mm.end()) * print.config().max_print_speed.value;
	        // limit such volumetric speed with max_volumetric_speed if set
            //BBS
	        //if (print.config().max_volumetric_speed.value > 0)
	        //    volumetric_speed = std::min(volumetric_speed, print.config().max_volumetric_speed.value);
	    }
	    return volumetric_speed;
	}
#endif

    static void init_ooze_prevention(const Print &print, OozePrevention &ooze_prevention)
	{
	    ooze_prevention.enable = print.config().ooze_prevention.value && ! print.config().single_extruder_multi_material;
	}

	// Fill in print_statistics and return formatted string containing filament statistics to be inserted into G-code comment section.
    static std::string update_print_stats_and_format_filament_stats(
        const bool                   has_wipe_tower,
	    const WipeTowerData         &wipe_tower_data,
	    const std::vector<Extruder> &extruders,
		PrintStatistics 		    &print_statistics)
    {
		std::string filament_stats_string_out;

	    print_statistics.clear();
        print_statistics.total_toolchanges = std::max(0, wipe_tower_data.number_of_toolchanges);
	    if (! extruders.empty()) {
	        std::pair<std::string, unsigned int> out_filament_used_mm ("; filament used [mm] = ", 0);
	        std::pair<std::string, unsigned int> out_filament_used_cm3("; filament used [cm3] = ", 0);
	        std::pair<std::string, unsigned int> out_filament_used_g  ("; filament used [g] = ", 0);
	        std::pair<std::string, unsigned int> out_filament_cost    ("; filament cost = ", 0);
	        for (const Extruder &extruder : extruders) {
	            double used_filament   = extruder.used_filament() + (has_wipe_tower ? wipe_tower_data.used_filament[extruder.id()] : 0.f);
	            double extruded_volume = extruder.extruded_volume() + (has_wipe_tower ? wipe_tower_data.used_filament[extruder.id()] * 2.4052f : 0.f); // assumes 1.75mm filament diameter
	            double filament_weight = extruded_volume * extruder.filament_density() * 0.001;
	            double filament_cost   = filament_weight * extruder.filament_cost()    * 0.001;
                auto append = [&extruder](std::pair<std::string, unsigned int> &dst, const char *tmpl, double value) {
                    assert(is_decimal_separator_point());
	                while (dst.second < extruder.id()) {
	                    // Fill in the non-printing extruders with zeros.
	                    dst.first += (dst.second > 0) ? ", 0" : "0";
	                    ++ dst.second;
	                }
	                if (dst.second > 0)
	                    dst.first += ", ";
	                char buf[64];
					sprintf(buf, tmpl, value);
	                dst.first += buf;
	                ++ dst.second;
	            };
	            append(out_filament_used_mm,  "%.2lf", used_filament);
	            append(out_filament_used_cm3, "%.2lf", extruded_volume * 0.001);
	            if (filament_weight > 0.) {
	                print_statistics.total_weight = print_statistics.total_weight + filament_weight;
	                append(out_filament_used_g, "%.2lf", filament_weight);
	                if (filament_cost > 0.) {
	                    print_statistics.total_cost = print_statistics.total_cost + filament_cost;
	                    append(out_filament_cost, "%.2lf", filament_cost);
	                }
	            }
	            print_statistics.total_used_filament += used_filament;
	            print_statistics.total_extruded_volume += extruded_volume;
	            print_statistics.total_wipe_tower_filament += has_wipe_tower ? used_filament - extruder.used_filament() : 0.;
	            print_statistics.total_wipe_tower_cost += has_wipe_tower ? (extruded_volume - extruder.extruded_volume())* extruder.filament_density() * 0.001 * extruder.filament_cost() * 0.001 : 0.;
	        }
	        filament_stats_string_out += out_filament_used_mm.first;
            filament_stats_string_out += "\n" + out_filament_used_cm3.first;
            if (out_filament_used_g.second)
                filament_stats_string_out += "\n" + out_filament_used_g.first;
            if (out_filament_cost.second)
               filament_stats_string_out += "\n" + out_filament_cost.first;
            filament_stats_string_out += "\n";
        }
        return filament_stats_string_out;
    }
}

#if 0
// Sort the PrintObjects by their increasing Z, likely useful for avoiding colisions on Deltas during sequential prints.
static inline std::vector<const PrintInstance*> sort_object_instances_by_max_z(const Print &print)
{
    std::vector<const PrintObject*> objects(print.objects().begin(), print.objects().end());
    std::sort(objects.begin(), objects.end(), [](const PrintObject *po1, const PrintObject *po2) { return po1->height() < po2->height(); });
    std::vector<const PrintInstance*> instances;
    instances.reserve(objects.size());
    for (const PrintObject *object : objects)
        for (size_t i = 0; i < object->instances().size(); ++ i)
            instances.emplace_back(&object->instances()[i]);
    return instances;
}
#endif

// Produce a vector of PrintObjects in the order of their respective ModelObjects in print.model().
//BBS: add sort logic for seq-print
std::vector<const PrintInstance*> sort_object_instances_by_model_order(const Print& print, bool init_order)
{
    auto find_object_index = [](const Model& model, const ModelObject* obj) {
        for (int index = 0; index < model.objects.size(); index++)
        {
            if (model.objects[index] == obj)
                return index;
        }
        return -1;
    };

    // Build up map from ModelInstance* to PrintInstance*
    std::vector<std::pair<const ModelInstance*, const PrintInstance*>> model_instance_to_print_instance;
    model_instance_to_print_instance.reserve(print.num_object_instances());
    for (const PrintObject *print_object : print.objects())
        for (const PrintInstance &print_instance : print_object->instances())
        {
            if (init_order)
                const_cast<ModelInstance*>(print_instance.model_instance)->arrange_order = find_object_index(print.model(), print_object->model_object());
            model_instance_to_print_instance.emplace_back(print_instance.model_instance, &print_instance);
        }
    std::sort(model_instance_to_print_instance.begin(), model_instance_to_print_instance.end(), [](auto &l, auto &r) { return l.first->arrange_order < r.first->arrange_order; });
    if (init_order) {
        // Re-assign the arrange_order so each instance has a unique order number
        for (int k = 0; k < model_instance_to_print_instance.size(); k++) {
            const_cast<ModelInstance*>(model_instance_to_print_instance[k].first)->arrange_order = k + 1;
        }
    }

    std::vector<const PrintInstance*> instances;
    instances.reserve(model_instance_to_print_instance.size());
    for (const ModelObject *model_object : print.model().objects)
        for (const ModelInstance *model_instance : model_object->instances) {
            auto it = std::lower_bound(model_instance_to_print_instance.begin(), model_instance_to_print_instance.end(), std::make_pair(model_instance, nullptr), [](auto &l, auto &r) { return l.first->arrange_order < r.first->arrange_order; });
            if (it != model_instance_to_print_instance.end() && it->first == model_instance)
                instances.emplace_back(it->second);
        }
    std::sort(instances.begin(), instances.end(), [](auto& l, auto& r) { return l->model_instance->arrange_order < r->model_instance->arrange_order; });
    return instances;
}

enum BambuBedType {
    bbtUnknown = 0,
    bbtCoolPlate = 1,
    bbtEngineeringPlate = 2,
    bbtHighTemperaturePlate = 3,
    bbtTexturedPEIPlate         = 4,
};

static BambuBedType to_bambu_bed_type(BedType type)
{
    BambuBedType bambu_bed_type = bbtUnknown;
    if (type == btPC)
        bambu_bed_type = bbtCoolPlate;
    else if (type == btEP)
        bambu_bed_type = bbtEngineeringPlate;
    else if (type == btPEI)
        bambu_bed_type = bbtHighTemperaturePlate;
    else if (type == btPTE)
        bambu_bed_type = bbtTexturedPEIPlate;
    else if (type == btPCT)
        bambu_bed_type = bbtCoolPlate;

    return bambu_bed_type;
}

void GCode::_do_export(Print& print, GCodeOutputStream &file, ThumbnailsGeneratorCallback thumbnail_cb)
{
    PROFILE_FUNC();

    // modifies m_silent_time_estimator_enabled
    DoExport::init_gcode_processor(print.config(), m_processor, m_silent_time_estimator_enabled);
    const bool is_bbl_printers = print.is_BBL_printer();
    m_calib_config.clear();
    // resets analyzer's tracking data
    m_last_height  = 0.f;
    m_last_layer_z = 0.f;
    m_max_layer_z  = 0.f;
    m_last_width = 0.f;
    m_is_overhang_fan_on = false;
    m_is_supp_interface_fan_on = false;
#if ENABLE_GCODE_VIEWER_DATA_CHECKING
    m_last_mm3_per_mm = 0.;
#endif // ENABLE_GCODE_VIEWER_DATA_CHECKING

    m_fan_mover.release();
    
    m_writer.set_is_bbl_machine(is_bbl_printers);

    // How many times will be change_layer() called?
    // change_layer() in turn increments the progress bar status.
    m_layer_count = 0;
    if (print.config().print_sequence == PrintSequence::ByObject) {
        // Add each of the object's layers separately.
        for (auto object : print.objects()) {
            std::vector<coordf_t> zs;
            zs.reserve(object->layers().size() + object->support_layers().size());
            for (auto layer : object->layers())
                zs.push_back(layer->print_z);
            for (auto layer : object->support_layers())
                zs.push_back(layer->print_z);
            std::sort(zs.begin(), zs.end());
            //BBS: merge numerically very close Z values.
            auto end_it = std::unique(zs.begin(), zs.end());
            unsigned int temp_layer_count = (unsigned int)(end_it - zs.begin());
            for (auto it = zs.begin(); it != end_it - 1; it++) {
                if (abs(*it - *(it + 1)) < EPSILON)
                    temp_layer_count--;
            }
            m_layer_count += (unsigned int)(object->instances().size() * temp_layer_count);
        }
    } else {
        // Print all objects with the same print_z together.
        std::vector<coordf_t> zs;
        for (auto object : print.objects()) {
            zs.reserve(zs.size() + object->layers().size() + object->support_layers().size());
            for (auto layer : object->layers())
                zs.push_back(layer->print_z);
            for (auto layer : object->support_layers())
                zs.push_back(layer->print_z);
        }
        if (!zs.empty())
        {
            std::sort(zs.begin(), zs.end());
            //BBS: merge numerically very close Z values.
            auto end_it = std::unique(zs.begin(), zs.end());
            m_layer_count = (unsigned int)(end_it - zs.begin());
            for (auto it = zs.begin(); it != end_it - 1; it++) {
                if (abs(*it - *(it + 1)) < EPSILON)
                    m_layer_count--;
            }
        }
    }
    print.throw_if_canceled();

    m_enable_cooling_markers = true;
    this->apply_print_config(print.config());

    //m_volumetric_speed = DoExport::autospeed_volumetric_limit(print);
    print.throw_if_canceled();

    if (print.config().spiral_mode.value)
        m_spiral_vase = make_unique<SpiralVase>(print.config());

    if (print.config().max_volumetric_extrusion_rate_slope.value > 0){
    		m_pressure_equalizer = make_unique<PressureEqualizer>(print.config());
    		m_enable_extrusion_role_markers = (bool)m_pressure_equalizer;
    } else
	    m_enable_extrusion_role_markers = false;

    if (!print.config().small_area_infill_flow_compensation_model.empty())
        m_small_area_infill_flow_compensator = make_unique<SmallAreaInfillFlowCompensator>(print.config());
    

    file.write_format("; HEADER_BLOCK_START\n");
    // Write information on the generator.
    file.write_format("; generated by %s on %s\n", Slic3r::header_slic3r_generated().c_str(), Slic3r::Utils::local_timestamp().c_str());
    if (is_bbl_printers)
        file.write_format(";%s\n", GCodeProcessor::reserved_tag(GCodeProcessor::ETags::Estimated_Printing_Time_Placeholder).c_str());
    //BBS: total layer number
    file.write_format(";%s\n", GCodeProcessor::reserved_tag(GCodeProcessor::ETags::Total_Layer_Number_Placeholder).c_str());
    m_enable_exclude_object = config().exclude_object;
    //Orca: extra check for bbl printer
    if (is_bbl_printers) {
        if (print.calib_params().mode == CalibMode::Calib_None) { // Don't support skipping in cali mode
            // list all label_object_id with sorted order here
            m_enable_exclude_object = true;
            m_label_objects_ids.clear();
            m_label_objects_ids.reserve(print.num_object_instances());
            for (const PrintObject *print_object : print.objects())
                for (const PrintInstance &print_instance : print_object->instances())
                    m_label_objects_ids.push_back(print_instance.model_instance->get_labeled_id());

            std::sort(m_label_objects_ids.begin(), m_label_objects_ids.end());

            std::string objects_id_list = "; model label id: ";
            for (auto it = m_label_objects_ids.begin(); it != m_label_objects_ids.end(); it++)
                objects_id_list += (std::to_string(*it) + (it != m_label_objects_ids.end() - 1 ? "," : "\n"));
            file.writeln(objects_id_list);
        } else {
            m_enable_exclude_object = false;
            m_label_objects_ids.clear();
        }
    }

    {
        std::string filament_density_list = "; filament_density: ";
        (filament_density_list+=m_config.filament_density.serialize()) +='\n';
        file.writeln(filament_density_list);

        std::string filament_diameter_list = "; filament_diameter: ";
        (filament_diameter_list += m_config.filament_diameter.serialize()) += '\n';
        file.writeln(filament_diameter_list);

        coordf_t max_height_z = -1;
        for (const auto& object : print.objects())
            max_height_z = std::max(object->layers().back()->print_z, max_height_z);

        std::ostringstream max_height_z_tip;
        max_height_z_tip<<"; max_z_height: " << std::fixed << std::setprecision(2) << max_height_z << '\n';
        file.writeln(max_height_z_tip.str());
    }

    file.write_format("; HEADER_BLOCK_END\n\n");

    
      // BBS: write global config at the beginning of gcode file because printer
      // need these config information
      // Append full config, delimited by two 'phony' configuration keys
      // CONFIG_BLOCK_START and CONFIG_BLOCK_END. The delimiters are structured
      // as configuration key / value pairs to be parsable by older versions of
      // PrusaSlicer G-code viewer.
    {
        if (is_bbl_printers) {
            file.write("; CONFIG_BLOCK_START\n");
            std::string full_config;
            append_full_config(print, full_config);
            if (!full_config.empty())
                file.write(full_config);

            // SoftFever: write compatiple image
            int first_layer_bed_temperature = get_bed_temperature(0, true, print.config().curr_bed_type);
            file.write_format("; first_layer_bed_temperature = %d\n",
                                first_layer_bed_temperature);
            file.write_format(
                "; first_layer_temperature = %d\n",
                print.config().nozzle_temperature_initial_layer.get_at(0));
            file.write("; CONFIG_BLOCK_END\n\n");
        } else if (thumbnail_cb != nullptr) {
            // generate the thumbnails
            auto [thumbnails, errors] = GCodeThumbnails::make_and_check_thumbnail_list(print.full_print_config());

            if (errors != enum_bitmask<ThumbnailError>()) {
                std::string error_str = format("Invalid thumbnails value:");
                error_str += GCodeThumbnails::get_error_string(errors);
                throw Slic3r::ExportError(error_str);
            }

            if (!thumbnails.empty())
                GCodeThumbnails::export_thumbnails_to_file(
                    thumbnail_cb, print.get_plate_index(), thumbnails, [&file](const char* sz) { file.write(sz); }, [&print]() { print.throw_if_canceled(); });
        }
    }


    // Write some terse information on the slicing parameters.
    const PrintObject *first_object         = print.objects().front();
    const double       layer_height         = first_object->config().layer_height.value;
    const double       initial_layer_print_height   = print.config().initial_layer_print_height.value;
    for (size_t region_id = 0; region_id < print.num_print_regions(); ++ region_id) {
        const PrintRegion &region = print.get_print_region(region_id);
        file.write_format("; external perimeters extrusion width = %.2fmm\n", region.flow(*first_object, frExternalPerimeter, layer_height).width());
        file.write_format("; perimeters extrusion width = %.2fmm\n",          region.flow(*first_object, frPerimeter,         layer_height).width());
        file.write_format("; infill extrusion width = %.2fmm\n",              region.flow(*first_object, frInfill,            layer_height).width());
        file.write_format("; solid infill extrusion width = %.2fmm\n",        region.flow(*first_object, frSolidInfill,       layer_height).width());
        file.write_format("; top infill extrusion width = %.2fmm\n",          region.flow(*first_object, frTopSolidInfill,    layer_height).width());
        if (print.has_support_material())
            file.write_format("; support material extrusion width = %.2fmm\n", support_material_flow(first_object).width());
        if (print.config().initial_layer_line_width.value > 0)
            file.write_format("; first layer extrusion width = %.2fmm\n",   region.flow(*first_object, frPerimeter, initial_layer_print_height, true).width());
        file.write_format("\n");
    }

    file.write_format("; EXECUTABLE_BLOCK_START\n");

    // SoftFever
    if( m_enable_exclude_object)
        file.write(set_object_info(&print));

    // adds tags for time estimators
    file.write_format(";%s\n", GCodeProcessor::reserved_tag(GCodeProcessor::ETags::First_Line_M73_Placeholder).c_str());

    // Prepare the helper object for replacing placeholders in custom G-code and output filename.
    m_placeholder_parser_integration.parser = print.placeholder_parser();
    m_placeholder_parser_integration.parser.update_timestamp();
    m_placeholder_parser_integration.context.rng = std::mt19937(std::chrono::high_resolution_clock::now().time_since_epoch().count());
    // Enable passing global variables between PlaceholderParser invocations.
    m_placeholder_parser_integration.context.global_config = std::make_unique<DynamicConfig>();
    print.update_object_placeholders(m_placeholder_parser_integration.parser.config_writable(), ".gcode");

    // Get optimal tool ordering to minimize tool switches of a multi-exruder print.
    // For a print by objects, find the 1st printing object.
    ToolOrdering tool_ordering;
    unsigned int initial_extruder_id = (unsigned int)-1;
    //BBS: first non-support filament extruder
    unsigned int initial_non_support_extruder_id;
    unsigned int final_extruder_id   = (unsigned int)-1;
    bool         has_wipe_tower      = false;
    std::vector<const PrintInstance*> 					print_object_instances_ordering;
    std::vector<const PrintInstance*>::const_iterator 	print_object_instance_sequential_active;
    if (print.config().print_sequence == PrintSequence::ByObject) {
        // Order object instances for sequential print.
        print_object_instances_ordering = sort_object_instances_by_model_order(print);
//        print_object_instances_ordering = sort_object_instances_by_max_z(print);
        // Find the 1st printing object, find its tool ordering and the initial extruder ID.
        print_object_instance_sequential_active = print_object_instances_ordering.begin();
        for (; print_object_instance_sequential_active != print_object_instances_ordering.end(); ++ print_object_instance_sequential_active) {
            tool_ordering = ToolOrdering(*(*print_object_instance_sequential_active)->print_object, initial_extruder_id);
            if ((initial_extruder_id = tool_ordering.first_extruder()) != static_cast<unsigned int>(-1)) {
                //BBS: try to find the non-support filament extruder if is multi color and initial_extruder is support filament
                initial_non_support_extruder_id = initial_extruder_id;
                if (tool_ordering.all_extruders().size() > 1 && print.config().filament_is_support.get_at(initial_extruder_id)) {
                    bool has_non_support_filament = false;
                    for (unsigned int extruder : tool_ordering.all_extruders()) {
                        if (!print.config().filament_is_support.get_at(extruder)) {
                            has_non_support_filament = true;
                            break;
                        }
                    }
                    //BBS: find the non-support filament extruder of object
                    if (has_non_support_filament)
                        for (LayerTools layer_tools : tool_ordering.layer_tools()) {
                            if (!layer_tools.has_object)
                                continue;
                            for (unsigned int extruder : layer_tools.extruders) {
                                if (print.config().filament_is_support.get_at(extruder))
                                    continue;
                                initial_non_support_extruder_id = extruder;
                                break;
                            }
                        }
                }

                break;
            }
        }
        if (initial_extruder_id == static_cast<unsigned int>(-1))
            // No object to print was found, cancel the G-code export.
            throw Slic3r::SlicingError(_(L("No object can be printed. Maybe too small")));
        // We don't allow switching of extruders per layer by Model::custom_gcode_per_print_z in sequential mode.
        // Use the extruder IDs collected from Regions.
        this->set_extruders(print.extruders());

        has_wipe_tower = print.has_wipe_tower() && tool_ordering.has_wipe_tower();
    } else {
        // Find tool ordering for all the objects at once, and the initial extruder ID.
        // If the tool ordering has been pre-calculated by Print class for wipe tower already, reuse it.
        tool_ordering = print.tool_ordering();
        tool_ordering.assign_custom_gcodes(print);
        if (tool_ordering.all_extruders().empty())
            // No object to print was found, cancel the G-code export.
            throw Slic3r::SlicingError(_(L("No object can be printed. Maybe too small")));
        has_wipe_tower = print.has_wipe_tower() && tool_ordering.has_wipe_tower();
        // Orca: support all extruder priming
        initial_extruder_id = (!is_bbl_printers && has_wipe_tower && !print.config().single_extruder_multi_material_priming) ?
            // The priming towers will be skipped.
            tool_ordering.all_extruders().back() :
            // Don't skip the priming towers.
            tool_ordering.first_extruder();

        //BBS: try to find the non-support filament extruder if is multi color and initial_extruder is support filament
        if (initial_extruder_id != static_cast<unsigned int>(-1)) {
            initial_non_support_extruder_id = initial_extruder_id;
            if (tool_ordering.all_extruders().size() > 1 && print.config().filament_is_support.get_at(initial_extruder_id)) {
                bool has_non_support_filament = false;
                for (unsigned int extruder : tool_ordering.all_extruders()) {
                    if (!print.config().filament_is_support.get_at(extruder)) {
                        has_non_support_filament = true;
                        break;
                    }
                }
                //BBS: find the non-support filament extruder of object
                if (has_non_support_filament)
                    for (LayerTools layer_tools : tool_ordering.layer_tools()) {
                        if (!layer_tools.has_object)
                            continue;
                        for (unsigned int extruder : layer_tools.extruders) {
                            if (print.config().filament_is_support.get_at(extruder))
                                continue;
                            initial_non_support_extruder_id = extruder;
                            break;
                        }
                    }
            }
        }

        // In non-sequential print, the printing extruders may have been modified by the extruder switches stored in Model::custom_gcode_per_print_z.
        // Therefore initialize the printing extruders from there.
        this->set_extruders(tool_ordering.all_extruders());
        print_object_instances_ordering = 
            // By default, order object instances using a nearest neighbor search.
            print.config().print_order == PrintOrder::Default ? chain_print_object_instances(print)
            // Otherwise same order as the object list
            : sort_object_instances_by_model_order(print);
    }
    if (initial_extruder_id == (unsigned int)-1) {
        // Nothing to print!
        initial_extruder_id = 0;
        initial_non_support_extruder_id = 0;
        final_extruder_id   = 0;
    } else {
        final_extruder_id = tool_ordering.last_extruder();
        assert(final_extruder_id != (unsigned int)-1);
    }
    print.throw_if_canceled();

    m_cooling_buffer = make_unique<CoolingBuffer>(*this);
    m_cooling_buffer->set_current_extruder(initial_extruder_id);
    
    // Orca: Initialise AdaptivePA processor filter
    m_pa_processor = std::make_unique<AdaptivePAProcessor>(*this, tool_ordering.all_extruders());

    // Emit machine envelope limits for the Marlin firmware.
    this->print_machine_envelope(file, print);

    // Disable fan.
    if (m_config.auxiliary_fan.value && print.config().close_fan_the_first_x_layers.get_at(initial_extruder_id)) {
        file.write(m_writer.set_fan(0));
        //BBS: disable additional fan
        file.write(m_writer.set_additional_fan(0));
    }

    // Update output variables after the extruders were initialized.
    m_placeholder_parser_integration.init(m_writer);
    // Let the start-up script prime the 1st printing tool.
    this->placeholder_parser().set("initial_tool", initial_extruder_id);
    this->placeholder_parser().set("initial_extruder", initial_extruder_id);
    //BBS
    this->placeholder_parser().set("initial_no_support_tool", initial_non_support_extruder_id);
    this->placeholder_parser().set("initial_no_support_extruder", initial_non_support_extruder_id);
    this->placeholder_parser().set("current_extruder", initial_extruder_id);
    //Orca: set the key for compatibilty
    this->placeholder_parser().set("retraction_distance_when_cut", m_config.retraction_distances_when_cut.get_at(initial_extruder_id));
    this->placeholder_parser().set("long_retraction_when_cut", m_config.long_retractions_when_cut.get_at(initial_extruder_id));
    this->placeholder_parser().set("temperature", new ConfigOptionInts(print.config().nozzle_temperature));


    this->placeholder_parser().set("retraction_distances_when_cut", new ConfigOptionFloats(m_config.retraction_distances_when_cut));
    this->placeholder_parser().set("long_retractions_when_cut",new ConfigOptionBools(m_config.long_retractions_when_cut));
    //Set variable for total layer count so it can be used in custom gcode.
    this->placeholder_parser().set("total_layer_count", m_layer_count);
    // Useful for sequential prints.
    this->placeholder_parser().set("current_object_idx", 0);
    // For the start / end G-code to do the priming and final filament pull in case there is no wipe tower provided.
    this->placeholder_parser().set("has_wipe_tower", has_wipe_tower);
    this->placeholder_parser().set("has_single_extruder_multi_material_priming", !is_bbl_printers && has_wipe_tower && print.config().single_extruder_multi_material_priming);
    this->placeholder_parser().set("total_toolchanges", std::max(0, print.wipe_tower_data().number_of_toolchanges)); // Check for negative toolchanges (single extruder mode) and set to 0 (no tool change).
    this->placeholder_parser().set("num_extruders", int(print.config().nozzle_diameter.values.size()));
    this->placeholder_parser().set("retract_length", new ConfigOptionFloats(print.config().retraction_length));

    //Orca: support max MAXIMUM_EXTRUDER_NUMBER extruders/filaments
    std::vector<unsigned char> is_extruder_used(std::max(size_t(MAXIMUM_EXTRUDER_NUMBER), print.config().filament_diameter.size()), 0);
    for (unsigned int extruder : tool_ordering.all_extruders())
        is_extruder_used[extruder] = true;
    this->placeholder_parser().set("is_extruder_used", new ConfigOptionBools(is_extruder_used));

    {
        BoundingBoxf bbox_bed(print.config().printable_area.values);
        Vec2f plate_offset = m_writer.get_xy_offset();
        this->placeholder_parser().set("print_bed_min", new ConfigOptionFloats({ bbox_bed.min.x(), bbox_bed.min.y()}));
        this->placeholder_parser().set("print_bed_max", new ConfigOptionFloats({ bbox_bed.max.x(), bbox_bed.max.y()}));
        this->placeholder_parser().set("print_bed_size", new ConfigOptionFloats({ bbox_bed.size().x(), bbox_bed.size().y() }));

        BoundingBoxf bbox;
        auto pts = std::make_unique<ConfigOptionPoints>();
        if (print.calib_mode() == CalibMode::Calib_PA_Line || print.calib_mode() == CalibMode::Calib_PA_Pattern) {
            bbox = bbox_bed;
            bbox.offset(-25.0);
            // add 4 corner points of bbox into pts
            pts->values.reserve(4);
            pts->values.emplace_back(bbox.min.x(), bbox.min.y());
            pts->values.emplace_back(bbox.max.x(), bbox.min.y());
            pts->values.emplace_back(bbox.max.x(), bbox.max.y());
            pts->values.emplace_back(bbox.min.x(), bbox.max.y());

        } else {
            // Convex hull of the 1st layer extrusions, for bed leveling and placing the initial purge line.
            // It encompasses the object extrusions, support extrusions, skirt, brim, wipe tower.
            // It does NOT encompass user extrusions generated by custom G-code,
            // therefore it does NOT encompass the initial purge line.
            // It does NOT encompass MMU/MMU2 starting (wipe) areas.
            pts->values.reserve(print.first_layer_convex_hull().size());
            for (const Point &pt : print.first_layer_convex_hull().points)
                pts->values.emplace_back(print.translate_to_print_space(pt));
            bbox = BoundingBoxf((pts->values));
        }
        this->placeholder_parser().set("first_layer_print_convex_hull", pts.release());
        this->placeholder_parser().set("first_layer_print_min", new ConfigOptionFloats({bbox.min.x(), bbox.min.y()}));
        this->placeholder_parser().set("first_layer_print_max", new ConfigOptionFloats({bbox.max.x(), bbox.max.y()}));
        this->placeholder_parser().set("first_layer_print_size", new ConfigOptionFloats({ bbox.size().x(), bbox.size().y() }));

        {  
            // use first layer convex_hull union with each object's bbox to check whether in head detect zone
            Polygons object_projections;
            for (auto& obj : print.objects()) {
                for (auto& instance : obj->instances()) {
                    const auto& bbox = instance.get_bounding_box();
                    Point min_p{ coord_t(scale_(bbox.min.x())),coord_t(scale_(bbox.min.y())) };
                    Point max_p{ coord_t(scale_(bbox.max.x())),coord_t(scale_(bbox.max.y())) };
                    Polygon instance_projection = {
                        {min_p.x(),min_p.y()},
                        {max_p.x(),min_p.y()},
                        {max_p.x(),max_p.y()},
                        {min_p.x(),max_p.y()}
                    };
                    object_projections.emplace_back(std::move(instance_projection));
                }
            }
            object_projections.emplace_back(print.first_layer_convex_hull());

            Polygons project_polys = union_(object_projections);
            Polygon  head_wrap_detect_zone;
            for (auto& point : print.config().head_wrap_detect_zone.values)
                head_wrap_detect_zone.append(scale_(point).cast<coord_t>() + scale_(plate_offset).cast<coord_t>());

            this->placeholder_parser().set("in_head_wrap_detect_zone", !intersection_pl(project_polys, {head_wrap_detect_zone}).empty());
        }

        BoundingBoxf mesh_bbox(m_config.bed_mesh_min, m_config.bed_mesh_max);
        auto         mesh_margin = m_config.adaptive_bed_mesh_margin.value;
        mesh_bbox.min            = mesh_bbox.min.cwiseMax((bbox.min.array() - mesh_margin).matrix());
        mesh_bbox.max            = mesh_bbox.max.cwiseMin((bbox.max.array() + mesh_margin).matrix());
        this->placeholder_parser().set("adaptive_bed_mesh_min", new ConfigOptionFloats({mesh_bbox.min.x(), mesh_bbox.min.y()}));
        this->placeholder_parser().set("adaptive_bed_mesh_max", new ConfigOptionFloats({mesh_bbox.max.x(), mesh_bbox.max.y()}));

        auto probe_dist_x  = std::max(1., m_config.bed_mesh_probe_distance.value.x());
        auto probe_dist_y  = std::max(1., m_config.bed_mesh_probe_distance.value.y());
        int  probe_count_x = std::max(3, (int) std::ceil(mesh_bbox.size().x() / probe_dist_x));
        int  probe_count_y = std::max(3, (int) std::ceil(mesh_bbox.size().y() / probe_dist_y));
        auto bed_mesh_algo = "bicubic";
        if (probe_count_x * probe_count_y <= 6) { // lagrange needs up to a total of 6 mesh points
            bed_mesh_algo = "lagrange";
        }
        else
            if(print.config().gcode_flavor == gcfKlipper){
              // bicubic needs 4 probe points per axis
              probe_count_x = std::max(probe_count_x,4);
              probe_count_y = std::max(probe_count_y,4);
            }
        this->placeholder_parser().set("bed_mesh_probe_count", new ConfigOptionInts({probe_count_x, probe_count_y}));
        this->placeholder_parser().set("bed_mesh_algo", bed_mesh_algo);
        // get center without wipe tower
        BoundingBoxf bbox_wo_wt; // bounding box without wipe tower
        for (auto &objPtr : print.objects()) {
            BBoxData data;
            bbox_wo_wt.merge(unscaled(objPtr->get_first_layer_bbox(data.area, data.layer_height, data.name)));
        }
        auto center = bbox_wo_wt.center();
        this->placeholder_parser().set("first_layer_center_no_wipe_tower", new ConfigOptionFloats{ {center.x(),center.y()}});
    }
    bool activate_chamber_temp_control = false;
    auto max_chamber_temp              = 0;
    for (const auto &extruder : m_writer.extruders()) {
        activate_chamber_temp_control |= m_config.activate_chamber_temp_control.get_at(extruder.id());
        max_chamber_temp = std::max(max_chamber_temp, m_config.chamber_temperature.get_at(extruder.id()));
    }
    float outer_wall_volumetric_speed = 0.0f;
    {
        int curr_bed_type = m_config.curr_bed_type.getInt();

        std::string first_layer_bed_temp_str;
        const ConfigOptionInts* first_bed_temp_opt = m_config.option<ConfigOptionInts>(get_bed_temp_1st_layer_key((BedType)curr_bed_type));
        const ConfigOptionInts* bed_temp_opt = m_config.option<ConfigOptionInts>(get_bed_temp_key((BedType)curr_bed_type));
        this->placeholder_parser().set("bbl_bed_temperature_gcode", new ConfigOptionBool(false));
        this->placeholder_parser().set("bed_temperature_initial_layer", new ConfigOptionInts(*first_bed_temp_opt));
        this->placeholder_parser().set("bed_temperature", new ConfigOptionInts(*bed_temp_opt));
        this->placeholder_parser().set("bed_temperature_initial_layer_single", new ConfigOptionInt(first_bed_temp_opt->get_at(initial_extruder_id)));
        this->placeholder_parser().set("bed_temperature_initial_layer_vector", new ConfigOptionString(""));
        this->placeholder_parser().set("chamber_temperature",new ConfigOptionInts(m_config.chamber_temperature));
        this->placeholder_parser().set("overall_chamber_temperature", new ConfigOptionInt(max_chamber_temp));

        // SoftFever: support variables `first_layer_temperature` and `first_layer_bed_temperature`
        this->placeholder_parser().set("first_layer_bed_temperature", new ConfigOptionInts(*first_bed_temp_opt));
        this->placeholder_parser().set("first_layer_temperature", new ConfigOptionInts(m_config.nozzle_temperature_initial_layer));
        this->placeholder_parser().set("max_print_height",new ConfigOptionInt(m_config.printable_height));
        this->placeholder_parser().set("z_offset", new ConfigOptionFloat(m_config.z_offset));
        this->placeholder_parser().set("model_name", new ConfigOptionString(print.get_model_name()));
        this->placeholder_parser().set("plate_number", new ConfigOptionString(print.get_plate_number_formatted()));
        this->placeholder_parser().set("plate_name", new ConfigOptionString(print.get_plate_name()));
        this->placeholder_parser().set("first_layer_height", new ConfigOptionFloat(m_config.initial_layer_print_height.value));

        //add during_print_exhaust_fan_speed
        std::vector<int> during_print_exhaust_fan_speed_num;
        during_print_exhaust_fan_speed_num.reserve(m_config.during_print_exhaust_fan_speed.size());
        for (const auto& item : m_config.during_print_exhaust_fan_speed.values)
            during_print_exhaust_fan_speed_num.emplace_back((int)(item / 100.0 * 255));
        this->placeholder_parser().set("during_print_exhaust_fan_speed_num",new ConfigOptionInts(during_print_exhaust_fan_speed_num));

        // calculate the volumetric speed of outer wall. Ignore per-object setting and multi-filament, and just use the default setting
        {

            float filament_max_volumetric_speed = m_config.option<ConfigOptionFloats>("filament_max_volumetric_speed")->get_at(initial_non_support_extruder_id);
            const double nozzle_diameter = m_config.nozzle_diameter.get_at(initial_non_support_extruder_id);
            float outer_wall_line_width = print.default_region_config().get_abs_value("outer_wall_line_width", nozzle_diameter);
            if (outer_wall_line_width == 0.0) {
                float default_line_width =  print.default_object_config().get_abs_value("line_width", nozzle_diameter);
                outer_wall_line_width = default_line_width == 0.0 ? nozzle_diameter : default_line_width;
            }
            Flow outer_wall_flow = Flow(outer_wall_line_width, m_config.layer_height, m_config.nozzle_diameter.get_at(initial_non_support_extruder_id));
            float outer_wall_speed = print.default_region_config().outer_wall_speed.value;
            outer_wall_volumetric_speed = outer_wall_speed * outer_wall_flow.mm3_per_mm();
            if (outer_wall_volumetric_speed > filament_max_volumetric_speed)
                outer_wall_volumetric_speed = filament_max_volumetric_speed;
            this->placeholder_parser().set("outer_wall_volumetric_speed", new ConfigOptionFloat(outer_wall_volumetric_speed));
        }

        if (print.calib_params().mode == CalibMode::Calib_PA_Line) {
            this->placeholder_parser().set("scan_first_layer", new ConfigOptionBool(false));
        }
    }
    std::string machine_start_gcode = this->placeholder_parser_process("machine_start_gcode", print.config().machine_start_gcode.value, initial_extruder_id);
    if (print.config().gcode_flavor != gcfKlipper) {
        // Set bed temperature if the start G-code does not contain any bed temp control G-codes.
        this->_print_first_layer_bed_temperature(file, print, machine_start_gcode, initial_extruder_id, true);
        // Set extruder(s) temperature before and after start G-code.
        this->_print_first_layer_extruder_temperatures(file, print, machine_start_gcode, initial_extruder_id, false);
    }

    // adds tag for processor
    file.write_format(";%s%s\n", GCodeProcessor::reserved_tag(GCodeProcessor::ETags::Role).c_str(), ExtrusionEntity::role_to_string(erCustom).c_str());

    // Orca: set chamber temperature at the beginning of gcode file
    if (activate_chamber_temp_control && max_chamber_temp > 0)
        file.write(m_writer.set_chamber_temperature(max_chamber_temp, true)); // set chamber_temperature

    // Write the custom start G-code
    file.writeln(machine_start_gcode);

    //BBS: gcode writer doesn't know where the real position of extruder is after inserting custom gcode
    m_writer.set_current_position_clear(false);
    m_start_gcode_filament = GCodeProcessor::get_gcode_last_filament(machine_start_gcode);

    //flush FanMover buffer to avoid modifying the start gcode if it's manual.
    if (!machine_start_gcode.empty() && this->m_fan_mover.get() != nullptr)
        file.write(this->m_fan_mover.get()->process_gcode("", true));

    // Process filament-specific gcode.
   /* if (has_wipe_tower) {
        // Wipe tower will control the extruder switching, it will call the filament_start_gcode.
    } else {
            DynamicConfig config;
            config.set_key_value("filament_extruder_id", new ConfigOptionInt(int(initial_extruder_id)));
            file.writeln(this->placeholder_parser_process("filament_start_gcode", print.config().filament_start_gcode.values[initial_extruder_id], initial_extruder_id, &config));
    }
*/
    if (is_bbl_printers) {
        this->_print_first_layer_extruder_temperatures(file, print, machine_start_gcode, initial_extruder_id, true);
    }
    // Orca: when activate_air_filtration is set on any extruder, find and set the highest during_print_exhaust_fan_speed
    bool activate_air_filtration        = false;
    int  during_print_exhaust_fan_speed = 0;
    for (const auto &extruder : m_writer.extruders()) {
        activate_air_filtration |= m_config.activate_air_filtration.get_at(extruder.id());
        if (m_config.activate_air_filtration.get_at(extruder.id()))
            during_print_exhaust_fan_speed = std::max(during_print_exhaust_fan_speed,
                                                      m_config.during_print_exhaust_fan_speed.get_at(extruder.id()));
    }
    if (activate_air_filtration)
        file.write(m_writer.set_exhaust_fan(during_print_exhaust_fan_speed, true));

    print.throw_if_canceled();

    // Set other general things.
    file.write(this->preamble());

    // Calculate wiping points if needed
    DoExport::init_ooze_prevention(print, m_ooze_prevention);
    print.throw_if_canceled();

    // Collect custom seam data from all objects.
    std::function<void(void)> throw_if_canceled_func = [&print]() { print.throw_if_canceled(); };
    m_seam_placer.init(print, throw_if_canceled_func);

    // BBS: get path for change filament
    if (m_writer.multiple_extruders) {
        std::vector<Vec2d> points = get_path_of_change_filament(print);
        if (points.size() == 3) {
            travel_point_1 = points[0];
            travel_point_2 = points[1];
            travel_point_3 = points[2];
        }
    }

    // Orca: support extruder priming
    if (is_bbl_printers || ! (has_wipe_tower && print.config().single_extruder_multi_material_priming))
    {
        // Set initial extruder only after custom start G-code.
        // Ugly hack: Do not set the initial extruder if the extruder is primed using the MMU priming towers at the edge of the print bed.
        file.write(this->set_extruder(initial_extruder_id, 0.));
    }
    // BBS: set that indicates objs with brim
    for (auto iter = print.m_brimMap.begin(); iter != print.m_brimMap.end(); ++iter) {
        if (!iter->second.empty())
            this->m_objsWithBrim.insert(iter->first);
    }
    for (auto iter = print.m_supportBrimMap.begin(); iter != print.m_supportBrimMap.end(); ++iter) {
        if (!iter->second.empty())
            this->m_objSupportsWithBrim.insert(iter->first);
    }
    if (this->m_objsWithBrim.empty() && this->m_objSupportsWithBrim.empty()) m_brim_done = true;

    // SoftFever: calib
    if (print.calib_params().mode == CalibMode::Calib_PA_Line) {
        std::string gcode;
        if ((print.default_object_config().outer_wall_acceleration.value > 0 && print.default_object_config().outer_wall_acceleration.value > 0)) {
            gcode += m_writer.set_print_acceleration((unsigned int)floor(print.default_object_config().outer_wall_acceleration.value + 0.5));
        }

        if (print.default_object_config().outer_wall_jerk.value > 0) {
            double jerk = print.default_object_config().outer_wall_jerk.value;
            gcode += m_writer.set_jerk_xy(jerk);
        }

        auto params = print.calib_params();

        CalibPressureAdvanceLine pa_test(this);

        auto fast_speed = CalibPressureAdvance::find_optimal_PA_speed(print.full_print_config(), pa_test.line_width(), pa_test.height_layer());
        auto slow_speed = std::max(10.0, fast_speed / 10.0);
        if (fast_speed < slow_speed + 5)
            fast_speed = slow_speed + 5;

        pa_test.set_speed(fast_speed, slow_speed);
        pa_test.draw_numbers() = print.calib_params().print_numbers;
        gcode += pa_test.generate_test(params.start, params.step, std::llround(std::ceil((params.end - params.start) / params.step)) + 1);

        file.write(gcode);
    } else {
        //BBS: open spaghetti detector
        if (is_bbl_printers) {
            // if (print.config().spaghetti_detector.value)
            file.write("M981 S1 P20000 ;open spaghetti detector\n");
        }

        // Do all objects for each layer.
        if (print.config().print_sequence == PrintSequence::ByObject && !has_wipe_tower) {
            size_t finished_objects = 0;
            const PrintObject *prev_object = (*print_object_instance_sequential_active)->print_object;
            for (; print_object_instance_sequential_active != print_object_instances_ordering.end(); ++ print_object_instance_sequential_active) {
                const PrintObject &object = *(*print_object_instance_sequential_active)->print_object;
                if (&object != prev_object || tool_ordering.first_extruder() != final_extruder_id) {
                    tool_ordering = ToolOrdering(object, final_extruder_id);
                    unsigned int new_extruder_id = tool_ordering.first_extruder();
                    if (new_extruder_id == (unsigned int)-1)
                        // Skip this object.
                        continue;
                    initial_extruder_id = new_extruder_id;
                    final_extruder_id   = tool_ordering.last_extruder();
                    assert(final_extruder_id != (unsigned int)-1);
                }
                print.throw_if_canceled();
                this->set_origin(unscale((*print_object_instance_sequential_active)->shift));

                // BBS: prime extruder if extruder change happens before this object instance
                bool prime_extruder = false;
                if (finished_objects > 0) {
                    // Move to the origin position for the copy we're going to print.
                    // This happens before Z goes down to layer 0 again, so that no collision happens hopefully.
                    m_enable_cooling_markers = false; // we're not filtering these moves through CoolingBuffer
                    m_avoid_crossing_perimeters.use_external_mp_once();
                    // BBS. change tool before moving to origin point.
                    if (m_writer.need_toolchange(initial_extruder_id)) {
                        const PrintObjectConfig& object_config = object.config();
                        coordf_t initial_layer_print_height = print.config().initial_layer_print_height.value;
                        file.write(this->set_extruder(initial_extruder_id, initial_layer_print_height, true));
                        prime_extruder = true;
                    }
                    else {
                        file.write(this->retract());
                    }
                    file.write(m_writer.travel_to_z(m_max_layer_z));
                    file.write(this->travel_to(Point(0, 0), erNone, "move to origin position for next object"));
                    m_enable_cooling_markers = true;
                    // Disable motion planner when traveling to first object point.
                    m_avoid_crossing_perimeters.disable_once();
                    // Ff we are printing the bottom layer of an object, and we have already finished
                    // another one, set first layer temperatures. This happens before the Z move
                    // is triggered, so machine has more time to reach such temperatures.
                    this->placeholder_parser().set("current_object_idx", int(finished_objects));
                    std::string printing_by_object_gcode = this->placeholder_parser_process("printing_by_object_gcode", print.config().printing_by_object_gcode.value, initial_extruder_id);
                    // Set first layer bed and extruder temperatures, don't wait for it to reach the temperature.
                    this->_print_first_layer_bed_temperature(file, print, printing_by_object_gcode, initial_extruder_id, false);
                    this->_print_first_layer_extruder_temperatures(file, print, printing_by_object_gcode, initial_extruder_id, false);
                    file.writeln(printing_by_object_gcode);
                }
                // Reset the cooling buffer internal state (the current position, feed rate, accelerations).
                m_cooling_buffer->reset(this->writer().get_position());
                m_cooling_buffer->set_current_extruder(initial_extruder_id);
                // Process all layers of a single object instance (sequential mode) with a parallel pipeline:
                // Generate G-code, run the filters (vase mode, cooling buffer), run the G-code analyser
                // and export G-code into file.
                this->process_layers(print, tool_ordering, collect_layers_to_print(object), *print_object_instance_sequential_active - object.instances().data(), file, prime_extruder);
                //BBS: close powerlost recovery
                {
                    if (is_bbl_printers && m_second_layer_things_done) {
                        file.write("; close powerlost recovery\n");
                        file.write("M1003 S0\n");
                    }
                }
                ++ finished_objects;
                // Flag indicating whether the nozzle temperature changes from 1st to 2nd layer were performed.
                // Reset it when starting another object from 1st layer.
                m_second_layer_things_done = false;
                prev_object = &object;
            }
        } else {
            // Sort layers by Z.
            // All extrusion moves with the same top layer height are extruded uninterrupted.
            std::vector<std::pair<coordf_t, std::vector<LayerToPrint>>> layers_to_print = collect_layers_to_print(print);
            // Prusa Multi-Material wipe tower.
            if (has_wipe_tower && ! layers_to_print.empty()) {
                m_wipe_tower.reset(new WipeTowerIntegration(print.config(), print.get_plate_index(), print.get_plate_origin(), * print.wipe_tower_data().priming.get(), print.wipe_tower_data().tool_changes, *print.wipe_tower_data().final_purge.get()));
                //BBS
                file.write(m_writer.travel_to_z(initial_layer_print_height + m_config.z_offset.value, "Move to the first layer height"));

                if (!is_bbl_printers && print.config().single_extruder_multi_material_priming) {
                    file.write(m_wipe_tower->prime(*this));
                    // Verify, whether the print overaps the priming extrusions.
                    BoundingBoxf bbox_print(get_print_extrusions_extents(print));
                    coordf_t twolayers_printz = ((layers_to_print.size() == 1) ? layers_to_print.front() : layers_to_print[1]).first + EPSILON;
                    for (const PrintObject *print_object : print.objects())
                        bbox_print.merge(get_print_object_extrusions_extents(*print_object, twolayers_printz));
                    bbox_print.merge(get_wipe_tower_extrusions_extents(print, twolayers_printz));
                    BoundingBoxf bbox_prime(get_wipe_tower_priming_extrusions_extents(print));
                    bbox_prime.offset(0.5f);
                    bool overlap = bbox_prime.overlap(bbox_print);

                    if (print.config().gcode_flavor == gcfMarlinLegacy || print.config().gcode_flavor == gcfMarlinFirmware) {
                        file.write(this->retract());
                        file.write("M300 S800 P500\n"); // Beep for 500ms, tone 800Hz.
                        if (overlap) {
                            // Wait for the user to remove the priming extrusions.
                            file.write("M1 Remove priming towers and click button.\n");
                        } else {
                            // Just wait for a bit to let the user check, that the priming succeeded.
                            //TODO Add a message explaining what the printer is waiting for. This needs a firmware fix.
                            file.write("M1 S10\n");
                        }
                    }
                    else {
                        // This is not Marlin, M1 command is probably not supported.
                        if (overlap) {
                           print.active_step_add_warning(PrintStateBase::WarningLevel::CRITICAL,
                               _(L("Your print is very close to the priming regions. "
                                 "Make sure there is no collision.")));
                        } else {
                           // Just continue printing, no action necessary.
                        }
                    }
                }
                print.throw_if_canceled();
            }
            // Process all layers of all objects (non-sequential mode) with a parallel pipeline:
            // Generate G-code, run the filters (vase mode, cooling buffer), run the G-code analyser
            // and export G-code into file.
            this->process_layers(print, tool_ordering, print_object_instances_ordering, layers_to_print, file);
            //BBS: close powerlost recovery
            {
                if (is_bbl_printers && m_second_layer_things_done) {
                    file.write("; close powerlost recovery\n");
                    file.write("M1003 S0\n");
                }
            }
            if (m_wipe_tower)
                // Purge the extruder, pull out the active filament.
                file.write(m_wipe_tower->finalize(*this));
        }
    }
    //BBS: the last retraction
    // Write end commands to file.
    file.write(this->retract(false, true));

    // if needed, write the gcode_label_objects_end
    {
        std::string gcode;
        m_writer.add_object_change_labels(gcode);
        file.write(gcode);
    }

    file.write(m_writer.set_fan(0));
    //BBS: make sure the additional fan is closed when end
    if(m_config.auxiliary_fan.value)
        file.write(m_writer.set_additional_fan(0));
    if (is_bbl_printers) {
        //BBS: close spaghetti detector
        //Note: M981 is also used to tell xcam the last layer is finished, so we need always send it even if spaghetti option is disabled.
        //if (print.config().spaghetti_detector.value)
        file.write("M981 S0 P20000 ; close spaghetti detector\n");
    }

    // adds tag for processor
    file.write_format(";%s%s\n", GCodeProcessor::reserved_tag(GCodeProcessor::ETags::Role).c_str(), ExtrusionEntity::role_to_string(erCustom).c_str());

    // Process filament-specific gcode in extruder order.
    {
        DynamicConfig config;
        config.set_key_value("layer_num", new ConfigOptionInt(m_layer_index));
        //BBS
        config.set_key_value("layer_z",   new ConfigOptionFloat(m_writer.get_position()(2) - m_config.z_offset.value));
        config.set_key_value("max_layer_z", new ConfigOptionFloat(m_max_layer_z));
        if (print.config().single_extruder_multi_material) {
            // Process the filament_end_gcode for the active filament only.
            int extruder_id = m_writer.extruder()->id();
            config.set_key_value("filament_extruder_id", new ConfigOptionInt(extruder_id));
            file.writeln(this->placeholder_parser_process("filament_end_gcode", print.config().filament_end_gcode.get_at(extruder_id), extruder_id, &config));
        } else {
            for (const std::string &end_gcode : print.config().filament_end_gcode.values) {
                int extruder_id = (unsigned int)(&end_gcode - &print.config().filament_end_gcode.values.front());
                config.set_key_value("filament_extruder_id", new ConfigOptionInt(extruder_id));
                file.writeln(this->placeholder_parser_process("filament_end_gcode", end_gcode, extruder_id, &config));
            }
        }
        file.writeln(this->placeholder_parser_process("machine_end_gcode", print.config().machine_end_gcode, m_writer.extruder()->id(), &config));
    }
    file.write(m_writer.update_progress(m_layer_count, m_layer_count, true)); // 100%
    file.write(m_writer.postamble());

    if (activate_chamber_temp_control && max_chamber_temp > 0)
        file.write(m_writer.set_chamber_temperature(0, false));  //close chamber_temperature

    if (activate_air_filtration) {
        int complete_print_exhaust_fan_speed = 0;
        for (const auto& extruder : m_writer.extruders())
            if (m_config.activate_air_filtration.get_at(extruder.id()))
                complete_print_exhaust_fan_speed = std::max(complete_print_exhaust_fan_speed, m_config.complete_print_exhaust_fan_speed.get_at(extruder.id()));
        file.write(m_writer.set_exhaust_fan(complete_print_exhaust_fan_speed, true));
    }
    // adds tags for time estimators
    file.write_format(";%s\n", GCodeProcessor::reserved_tag(GCodeProcessor::ETags::Last_Line_M73_Placeholder).c_str());
    file.write_format("; EXECUTABLE_BLOCK_END\n\n");

    print.throw_if_canceled();

    // Get filament stats.
    file.write(DoExport::update_print_stats_and_format_filament_stats(
    	// Const inputs
        has_wipe_tower, print.wipe_tower_data(),
        m_writer.extruders(),
        // Modifies
        print.m_print_statistics));
    print.m_print_statistics.initial_tool = initial_extruder_id;
    if (!is_bbl_printers) {
        file.write_format("; total filament used [g] = %.2lf\n",
            print.m_print_statistics.total_weight);
        file.write_format("; total filament cost = %.2lf\n",
            print.m_print_statistics.total_cost);
        if (print.m_print_statistics.total_toolchanges > 0)
            file.write_format("; total filament change = %i\n",
                print.m_print_statistics.total_toolchanges);
        file.write_format("; total layers count = %i\n", m_layer_count);
        file.write_format(
            ";%s\n",
            GCodeProcessor::reserved_tag(
                GCodeProcessor::ETags::Estimated_Printing_Time_Placeholder)
            .c_str());
      file.write("\n");
      file.write("; CONFIG_BLOCK_START\n");
      std::string full_config;
      append_full_config(print, full_config);
      if (!full_config.empty())
        file.write(full_config);

      // SoftFever: write compatiple info
      int first_layer_bed_temperature = get_bed_temperature(0, true, print.config().curr_bed_type);
      file.write_format("; first_layer_bed_temperature = %d\n", first_layer_bed_temperature);
      file.write_format("; bed_shape = %s\n", print.full_print_config().opt_serialize("printable_area").c_str());
      file.write_format("; first_layer_temperature = %d\n", print.config().nozzle_temperature_initial_layer.get_at(0));
      file.write_format("; first_layer_height = %.3f\n", print.config().initial_layer_print_height.value);
        
        //SF TODO
//      file.write_format("; variable_layer_height = %d\n", print.ad.adaptive_layer_height ? 1 : 0);
   
      file.write("; CONFIG_BLOCK_END\n\n");

    }
    file.write("\n");

    print.throw_if_canceled();
}

//BBS
void GCode::check_placeholder_parser_failed()
{
    if (! m_placeholder_parser_integration.failed_templates.empty()) {
        // G-code export proceeded, but some of the PlaceholderParser substitutions failed.
        std::string msg = Slic3r::format(_(L("Failed to generate gcode for invalid custom G-code.\n\n")));
        for (const auto &name_and_error : m_placeholder_parser_integration.failed_templates)
            msg += name_and_error.first + " " + name_and_error.second + "\n";
        msg += Slic3r::format(_(L("Please check the custom G-code or use the default custom G-code.")));
        throw Slic3r::PlaceholderParserError(msg);
    }
}

// Process all layers of all objects (non-sequential mode) with a parallel pipeline:
// Generate G-code, run the filters (vase mode, cooling buffer), run the G-code analyser
// and export G-code into file.
void GCode::process_layers(
    const Print                                                         &print,
    const ToolOrdering                                                  &tool_ordering,
    const std::vector<const PrintInstance*>                             &print_object_instances_ordering,
    const std::vector<std::pair<coordf_t, std::vector<LayerToPrint>>>   &layers_to_print,
    GCodeOutputStream                                                   &output_stream)
{
    // The pipeline is variable: The vase mode filter is optional.
    size_t layer_to_print_idx = 0;
    const auto generator = tbb::make_filter<void, LayerResult>(slic3r_tbb_filtermode::serial_in_order,
        [this, &print, &tool_ordering, &print_object_instances_ordering, &layers_to_print, &layer_to_print_idx](tbb::flow_control& fc) -> LayerResult {
            if (layer_to_print_idx >= layers_to_print.size()) {
                if (layer_to_print_idx == layers_to_print.size() + (m_pressure_equalizer ? 1 : 0)) {
                    fc.stop();
                    return {};
                } else {
                    // Pressure equalizer need insert empty input. Because it returns one layer back.
                    // Insert NOP (no operation) layer;
                    ++layer_to_print_idx;
                    return LayerResult::make_nop_layer_result();
                }
            } else {
                const std::pair<coordf_t, std::vector<LayerToPrint>>& layer = layers_to_print[layer_to_print_idx++];
                const LayerTools& layer_tools = tool_ordering.tools_for_layer(layer.first);
                print.set_status(80, Slic3r::format(_(L("Generating G-code: layer %1%")), std::to_string(layer_to_print_idx)));
                if (m_wipe_tower && layer_tools.has_wipe_tower)
                    m_wipe_tower->next_layer();
                //BBS
                check_placeholder_parser_failed();
                print.throw_if_canceled();
                return this->process_layer(print, layer.second, layer_tools, &layer == &layers_to_print.back(), &print_object_instances_ordering, size_t(-1));
            }
        });
    if (m_spiral_vase) {
        float nozzle_diameter  = EXTRUDER_CONFIG(nozzle_diameter);
        float max_xy_smoothing = m_config.get_abs_value("spiral_mode_max_xy_smoothing", nozzle_diameter);
        this->m_spiral_vase->set_max_xy_smoothing(max_xy_smoothing);
    }
    const auto spiral_mode = tbb::make_filter<LayerResult, LayerResult>(slic3r_tbb_filtermode::serial_in_order,
        [&spiral_mode = *this->m_spiral_vase.get(), &layers_to_print](LayerResult in) -> LayerResult {
        	if (in.nop_layer_result)
                return in;
                
            spiral_mode.enable(in.spiral_vase_enable);
            bool last_layer = in.layer_id == layers_to_print.size() - 1;
            return { spiral_mode.process_layer(std::move(in.gcode), last_layer), in.layer_id, in.spiral_vase_enable, in.cooling_buffer_flush};
        });
    const auto pressure_equalizer = tbb::make_filter<LayerResult, LayerResult>(slic3r_tbb_filtermode::serial_in_order,
        [pressure_equalizer = this->m_pressure_equalizer.get()](LayerResult in) -> LayerResult {
            return pressure_equalizer->process_layer(std::move(in));
        });
    const auto cooling = tbb::make_filter<LayerResult, std::string>(slic3r_tbb_filtermode::serial_in_order,
        [&cooling_buffer = *this->m_cooling_buffer.get()](LayerResult in) -> std::string {
        	if (in.nop_layer_result)
                return in.gcode;
            return cooling_buffer.process_layer(std::move(in.gcode), in.layer_id, in.cooling_buffer_flush);
        });
    const auto pa_processor_filter = tbb::make_filter<std::string, std::string>(slic3r_tbb_filtermode::serial_in_order,
            [&pa_processor = *this->m_pa_processor](std::string in) -> std::string {
                return pa_processor.process_layer(std::move(in));
            }
        );
    
    const auto output = tbb::make_filter<std::string, void>(slic3r_tbb_filtermode::serial_in_order,
        [&output_stream](std::string s) { output_stream.write(s); }
    );

    const auto fan_mover = tbb::make_filter<std::string, std::string>(slic3r_tbb_filtermode::serial_in_order,
            [&fan_mover = this->m_fan_mover, &config = this->config(), &writer = this->m_writer](std::string in)->std::string {

        CNumericLocalesSetter locales_setter;

        if (config.fan_speedup_time.value != 0 || config.fan_kickstart.value > 0) {
            if (fan_mover.get() == nullptr)
                fan_mover.reset(new Slic3r::FanMover(
                    writer,
                    std::abs((float)config.fan_speedup_time.value),
                    config.fan_speedup_time.value > 0,
                    config.use_relative_e_distances.value,
                    config.fan_speedup_overhangs.value,
                    (float)config.fan_kickstart.value));
            //flush as it's a whole layer
            return fan_mover->process_gcode(in, true);
        }
        return in;
    });

    // The pipeline elements are joined using const references, thus no copying is performed.
    if (m_spiral_vase && m_pressure_equalizer)
        tbb::parallel_pipeline(12, generator & spiral_mode & pressure_equalizer & cooling & fan_mover & output);
    else if (m_spiral_vase)
    	tbb::parallel_pipeline(12, generator & spiral_mode & cooling & fan_mover & output);
    else if	(m_pressure_equalizer)
        tbb::parallel_pipeline(12, generator & pressure_equalizer & cooling & fan_mover & pa_processor_filter & output);
    else
    	tbb::parallel_pipeline(12, generator & cooling & fan_mover & pa_processor_filter & output);
}

// Process all layers of a single object instance (sequential mode) with a parallel pipeline:
// Generate G-code, run the filters (vase mode, cooling buffer), run the G-code analyser
// and export G-code into file.
void GCode::process_layers(
    const Print                             &print,
    const ToolOrdering                      &tool_ordering,
    std::vector<LayerToPrint>                layers_to_print,
    const size_t                             single_object_idx,
    GCodeOutputStream                       &output_stream,
    // BBS
    const bool                               prime_extruder)
{
    // The pipeline is variable: The vase mode filter is optional.
    size_t layer_to_print_idx = 0;
    const auto generator = tbb::make_filter<void, LayerResult>(slic3r_tbb_filtermode::serial_in_order,
        [this, &print, &tool_ordering, &layers_to_print, &layer_to_print_idx, single_object_idx, prime_extruder](tbb::flow_control& fc) -> LayerResult {
            if (layer_to_print_idx >= layers_to_print.size()) {
                if (layer_to_print_idx == layers_to_print.size() + (m_pressure_equalizer ? 1 : 0)) {
                    fc.stop();
                    return {};
                } else {
                    // Pressure equalizer need insert empty input. Because it returns one layer back.
                    // Insert NOP (no operation) layer;
                    ++layer_to_print_idx;
                    return LayerResult::make_nop_layer_result();
                }
            } else {
                LayerToPrint &layer = layers_to_print[layer_to_print_idx ++];
                print.set_status(80, Slic3r::format(_(L("Generating G-code: layer %1%")), std::to_string(layer_to_print_idx)));
                //BBS
                check_placeholder_parser_failed();
                print.throw_if_canceled();
                return this->process_layer(print, { std::move(layer) }, tool_ordering.tools_for_layer(layer.print_z()), &layer == &layers_to_print.back(), nullptr, single_object_idx, prime_extruder);
            }
        });
    if (m_spiral_vase) {
        float nozzle_diameter  = EXTRUDER_CONFIG(nozzle_diameter);
        float max_xy_smoothing = m_config.get_abs_value("spiral_mode_max_xy_smoothing", nozzle_diameter);
        this->m_spiral_vase->set_max_xy_smoothing(max_xy_smoothing);
    }
    const auto spiral_mode = tbb::make_filter<LayerResult, LayerResult>(slic3r_tbb_filtermode::serial_in_order,
        [&spiral_mode = *this->m_spiral_vase.get(), &layers_to_print](LayerResult in)->LayerResult {
            if (in.nop_layer_result)
                return in;
            spiral_mode.enable(in.spiral_vase_enable);
            bool last_layer = in.layer_id == layers_to_print.size() - 1;
            return { spiral_mode.process_layer(std::move(in.gcode), last_layer), in.layer_id, in.spiral_vase_enable, in.cooling_buffer_flush };
        });
    const auto pressure_equalizer = tbb::make_filter<LayerResult, LayerResult>(slic3r_tbb_filtermode::serial_in_order,
        [pressure_equalizer = this->m_pressure_equalizer.get()](LayerResult in) -> LayerResult {
             return pressure_equalizer->process_layer(std::move(in));
        });
    const auto cooling = tbb::make_filter<LayerResult, std::string>(slic3r_tbb_filtermode::serial_in_order,
        [&cooling_buffer = *this->m_cooling_buffer.get()](LayerResult in)->std::string {
            if (in.nop_layer_result)
                return in.gcode;
            return cooling_buffer.process_layer(std::move(in.gcode), in.layer_id, in.cooling_buffer_flush);
        });
    const auto output = tbb::make_filter<std::string, void>(slic3r_tbb_filtermode::serial_in_order,
        [&output_stream](std::string s) { output_stream.write(s); }
    );

    const auto fan_mover = tbb::make_filter<std::string, std::string>(slic3r_tbb_filtermode::serial_in_order,
        [&fan_mover = this->m_fan_mover, &config = this->config(), &writer = this->m_writer](std::string in)->std::string {

        if (config.fan_speedup_time.value != 0 || config.fan_kickstart.value > 0) {
            if (fan_mover.get() == nullptr)
                fan_mover.reset(new Slic3r::FanMover(
                    writer,
                    std::abs((float)config.fan_speedup_time.value),
                    config.fan_speedup_time.value > 0,
                    config.use_relative_e_distances.value,
                    config.fan_speedup_overhangs.value,
                    (float)config.fan_kickstart.value));
            //flush as it's a whole layer
            return fan_mover->process_gcode(in, true);
        }
        return in;
    });

    // The pipeline elements are joined using const references, thus no copying is performed.
    if (m_spiral_vase && m_pressure_equalizer)
        tbb::parallel_pipeline(12, generator & spiral_mode & pressure_equalizer & cooling & fan_mover & output);
    else if (m_spiral_vase)
    	tbb::parallel_pipeline(12, generator & spiral_mode & cooling & fan_mover & output);
    else if	(m_pressure_equalizer)
        tbb::parallel_pipeline(12, generator & pressure_equalizer & cooling & fan_mover & output);
    else
    	tbb::parallel_pipeline(12, generator & cooling & fan_mover & output);
}

std::string GCode::placeholder_parser_process(const std::string &name, const std::string &templ, unsigned int current_extruder_id, const DynamicConfig *config_override)
{
    // Orca: Added CMake config option since debug is rarely used in current workflow.
    // Also changed from throwing error immediately to storing messages till slicing is completed
    // to raise all errors at the same time.
#if ORCA_CHECK_GCODE_PLACEHOLDERS
    if (config_override) {
        const auto& custom_gcode_placeholders = custom_gcode_specific_placeholders();

        // 1-st check: custom G-code "name" have to be present in s_CustomGcodeSpecificOptions;
        //if (custom_gcode_placeholders.count(name) > 0) {
        //    const auto& placeholders = custom_gcode_placeholders.at(name);
        if (auto it = custom_gcode_placeholders.find(name); it != custom_gcode_placeholders.end()) {
            const auto& placeholders = it->second;

            for (const std::string& key : config_override->keys()) {
                // 2-nd check: "key" have to be present in s_CustomGcodeSpecificOptions for "name" custom G-code ;
                if (std::find(placeholders.begin(), placeholders.end(), key) == placeholders.end()) {
                    auto& vector = m_placeholder_error_messages[name + " - option not specified for custom gcode type (s_CustomGcodeSpecificOptions)"];
                    if (std::find(vector.begin(), vector.end(), key) == vector.end())
                        vector.emplace_back(key);
                }
                // 3-rd check: "key" have to be present in CustomGcodeSpecificConfigDef for "key" placeholder;
                if (!custom_gcode_specific_config_def.has(key)) {
                    auto& vector = m_placeholder_error_messages[name + " - option has no definition (CustomGcodeSpecificConfigDef)"];
                    if (std::find(vector.begin(), vector.end(), key) == vector.end())
                        vector.emplace_back(key);
                }
            }
        }
        else {
            auto& vector = m_placeholder_error_messages[name + " - gcode type not found in s_CustomGcodeSpecificOptions"];
            if (vector.empty())
                vector.emplace_back("");
        }
    }
#endif

PlaceholderParserIntegration &ppi = m_placeholder_parser_integration;
    try {
        ppi.update_from_gcodewriter(m_writer);
        std::string output = ppi.parser.process(templ, current_extruder_id, config_override, &ppi.output_config, &ppi.context);
        ppi.validate_output_vector_variables();

        if (const std::vector<double> &pos = ppi.opt_position->values; ppi.position != pos) {
            // Update G-code writer.
            m_writer.set_position({ pos[0], pos[1], pos[2] });
            this->set_last_pos(this->gcode_to_point({ pos[0], pos[1] }));
        }

        for (const Extruder &e : m_writer.extruders()) {
            unsigned int eid = e.id();
            assert(eid < ppi.num_extruders);
            if ( eid < ppi.num_extruders) {
                if (! m_writer.config.use_relative_e_distances && ! is_approx(ppi.e_position[eid], ppi.opt_e_position->values[eid]))
                    const_cast<Extruder&>(e).set_position(ppi.opt_e_position->values[eid]);
                if (! is_approx(ppi.e_retracted[eid], ppi.opt_e_retracted->values[eid]) || 
                    ! is_approx(ppi.e_restart_extra[eid], ppi.opt_e_restart_extra->values[eid]))
                    const_cast<Extruder&>(e).set_retracted(ppi.opt_e_retracted->values[eid], ppi.opt_e_restart_extra->values[eid]);
            }
        }

        return output;
    } 
    catch (std::runtime_error &err) 
    {
        // Collect the names of failed template substitutions for error reporting.
        auto it = ppi.failed_templates.find(name);
        if (it == ppi.failed_templates.end())
            // Only if there was no error reported for this template, store the first error message into the map to be reported.
            // We don't want to collect error message for each and every occurence of a single custom G-code section.
            ppi.failed_templates.insert(it, std::make_pair(name, std::string(err.what())));
        // Insert the macro error message into the G-code.
        return
            std::string("\n!!!!! Failed to process the custom G-code template ") + name + "\n" +
            err.what() +
            "!!!!! End of an error report for the custom G-code template " + name + "\n\n";
    }
}

// Parse the custom G-code, try to find mcode_set_temp_dont_wait and mcode_set_temp_and_wait or optionally G10 with temperature inside the custom G-code.
// Returns true if one of the temp commands are found, and try to parse the target temperature value into temp_out.
static bool custom_gcode_sets_temperature(const std::string &gcode, const int mcode_set_temp_dont_wait, const int mcode_set_temp_and_wait, const bool include_g10, int &temp_out)
{
    temp_out = -1;
    if (gcode.empty())
        return false;

    const char *ptr = gcode.data();
    bool temp_set_by_gcode = false;
    while (*ptr != 0) {
        // Skip whitespaces.
        for (; *ptr == ' ' || *ptr == '\t'; ++ ptr);
        if (*ptr == 'M' || // Line starts with 'M'. It is a machine command.
            (*ptr == 'G' && include_g10)) { // Only check for G10 if requested
            bool is_gcode = *ptr == 'G';
            ++ ptr;
            // Parse the M or G code value.
            char *endptr = nullptr;
            int mgcode = int(strtol(ptr, &endptr, 10));
            if (endptr != nullptr && endptr != ptr &&
                is_gcode ?
                    // G10 found
                    mgcode == 10 :
                    // M104/M109 or M140/M190 found.
                    (mgcode == mcode_set_temp_dont_wait || mgcode == mcode_set_temp_and_wait)) {
                ptr = endptr;
                if (! is_gcode)
                    // Let the caller know that the custom M-code sets the temperature.
                    temp_set_by_gcode = true;
                // Now try to parse the temperature value.
                // While not at the end of the line:
                while (strchr(";\r\n\0", *ptr) == nullptr) {
                    // Skip whitespaces.
                    for (; *ptr == ' ' || *ptr == '\t'; ++ ptr);
                    if (*ptr == 'S') {
                        // Skip whitespaces.
                        for (++ ptr; *ptr == ' ' || *ptr == '\t'; ++ ptr);
                        // Parse an int.
                        endptr = nullptr;
                        long temp_parsed = strtol(ptr, &endptr, 10);
                        if (endptr > ptr) {
                            ptr = endptr;
                            temp_out = temp_parsed;
                            // Let the caller know that the custom G-code sets the temperature
                            // Only do this after successfully parsing temperature since G10
                            // can be used for other reasons
                            temp_set_by_gcode = true;
                        }
                    } else {
                        // Skip this word.
                        for (; strchr(" \t;\r\n\0", *ptr) == nullptr; ++ ptr);
                    }
                }
            }
        }
        // Skip the rest of the line.
        for (; *ptr != 0 && *ptr != '\r' && *ptr != '\n'; ++ ptr);
        // Skip the end of line indicators.
        for (; *ptr == '\r' || *ptr == '\n'; ++ ptr);
    }
    return temp_set_by_gcode;
}

// Print the machine envelope G-code for the Marlin firmware based on the "machine_max_xxx" parameters.
// Do not process this piece of G-code by the time estimator, it already knows the values through another sources.
void GCode::print_machine_envelope(GCodeOutputStream &file, Print &print)
{
    const auto flavor = print.config().gcode_flavor.value;
    if ((flavor == gcfMarlinLegacy || flavor == gcfMarlinFirmware || flavor == gcfRepRapFirmware) &&
        print.config().emit_machine_limits_to_gcode.value == true) {
        int factor = flavor == gcfRepRapFirmware ? 60 : 1; // RRF M203 and M566 are in mm/min
        file.write_format("M201 X%d Y%d Z%d E%d\n",
            int(print.config().machine_max_acceleration_x.values.front() + 0.5),
            int(print.config().machine_max_acceleration_y.values.front() + 0.5),
            int(print.config().machine_max_acceleration_z.values.front() + 0.5),
            int(print.config().machine_max_acceleration_e.values.front() + 0.5));
        file.write_format("M203 X%d Y%d Z%d E%d\n",
            int(print.config().machine_max_speed_x.values.front() * factor + 0.5),
            int(print.config().machine_max_speed_y.values.front() * factor + 0.5),
            int(print.config().machine_max_speed_z.values.front() * factor + 0.5),
            int(print.config().machine_max_speed_e.values.front() * factor + 0.5));

        // Now M204 - acceleration. This one is quite hairy thanks to how Marlin guys care about
        // Legacy Marlin should export travel acceleration the same as printing acceleration.
        // MarlinFirmware has the two separated.
        int travel_acc = flavor == gcfMarlinLegacy
                       ? int(print.config().machine_max_acceleration_extruding.values.front() + 0.5)
                       : int(print.config().machine_max_acceleration_travel.values.front() + 0.5);
        if (flavor == gcfRepRapFirmware)
            file.write_format("M204 P%d T%d ; sets acceleration (P, T), mm/sec^2\n",
                int(print.config().machine_max_acceleration_extruding.values.front() + 0.5),
                travel_acc);
        else if (flavor == gcfMarlinFirmware)
            // New Marlin uses M204 P[print] R[retract] T[travel]
            file.write_format("M204 P%d R%d T%d ; sets acceleration (P, T) and retract acceleration (R), mm/sec^2\n",
                int(print.config().machine_max_acceleration_extruding.values.front() + 0.5),
                int(print.config().machine_max_acceleration_retracting.values.front() + 0.5),
                int(print.config().machine_max_acceleration_travel.values.front() + 0.5));
        else
            file.write_format("M204 P%d R%d T%d\n",
                int(print.config().machine_max_acceleration_extruding.values.front() + 0.5),
                int(print.config().machine_max_acceleration_retracting.values.front() + 0.5),
                travel_acc);

        assert(is_decimal_separator_point());
        file.write_format(flavor == gcfRepRapFirmware
            ? "M566 X%.2lf Y%.2lf Z%.2lf E%.2lf ; sets the jerk limits, mm/min\n"
            : "M205 X%.2lf Y%.2lf Z%.2lf E%.2lf ; sets the jerk limits, mm/sec\n",
            print.config().machine_max_jerk_x.values.front() * factor,
            print.config().machine_max_jerk_y.values.front() * factor,
            print.config().machine_max_jerk_z.values.front() * factor,
            print.config().machine_max_jerk_e.values.front() * factor);
    }
}

// BBS
int GCode::get_bed_temperature(const int extruder_id, const bool is_first_layer, const BedType bed_type) const
{
    std::string bed_temp_key = is_first_layer ? get_bed_temp_1st_layer_key(bed_type) : get_bed_temp_key(bed_type);
    const ConfigOptionInts* bed_temp_opt = m_config.option<ConfigOptionInts>(bed_temp_key);
    return bed_temp_opt->get_at(extruder_id);
}


// Write 1st layer bed temperatures into the G-code.
// Only do that if the start G-code does not already contain any M-code controlling an extruder temperature.
// M140 - Set Extruder Temperature
// M190 - Set Extruder Temperature and Wait
void GCode::_print_first_layer_bed_temperature(GCodeOutputStream &file, Print &print, const std::string &gcode, unsigned int first_printing_extruder_id, bool wait)
{
    // Initial bed temperature based on the first extruder.
    // BBS
    std::vector<int> temps_per_bed;
    int bed_temp = get_bed_temperature(first_printing_extruder_id, true, print.config().curr_bed_type);

    // Is the bed temperature set by the provided custom G-code?
    int  temp_by_gcode     = -1;
    bool temp_set_by_gcode = custom_gcode_sets_temperature(gcode, 140, 190, false, temp_by_gcode);
    // BBS
#if 0
    if (temp_set_by_gcode && temp_by_gcode >= 0 && temp_by_gcode < 1000)
        temp = temp_by_gcode;
#endif

    // Always call m_writer.set_bed_temperature() so it will set the internal "current" state of the bed temp as if
    // the custom start G-code emited these.
    std::string set_temp_gcode = m_writer.set_bed_temperature(bed_temp, wait);
    if (! temp_set_by_gcode)
        file.write(set_temp_gcode);
}

// Write 1st layer extruder temperatures into the G-code.
// Only do that if the start G-code does not already contain any M-code controlling an extruder temperature.
// M104 - Set Extruder Temperature
// M109 - Set Extruder Temperature and Wait
// RepRapFirmware: G10 Sxx
void GCode::_print_first_layer_extruder_temperatures(GCodeOutputStream &file, Print &print, const std::string &gcode, unsigned int first_printing_extruder_id, bool wait)
{
    // Is the bed temperature set by the provided custom G-code?
    int  temp_by_gcode = -1;
    bool include_g10   = print.config().gcode_flavor == gcfRepRapFirmware;
    if (custom_gcode_sets_temperature(gcode, 104, 109, include_g10, temp_by_gcode)) {
        // Set the extruder temperature at m_writer, but throw away the generated G-code as it will be written with the custom G-code.
        int temp = print.config().nozzle_temperature_initial_layer.get_at(first_printing_extruder_id);
        if (temp_by_gcode >= 0 && temp_by_gcode < 1000)
            temp = temp_by_gcode;
        m_writer.set_temperature(temp, wait, first_printing_extruder_id);
    } else {
        // Custom G-code does not set the extruder temperature. Do it now.
        if (print.config().single_extruder_multi_material.value) {
            // Set temperature of the first printing extruder only.
            int temp = print.config().nozzle_temperature_initial_layer.get_at(first_printing_extruder_id);
            if (temp > 0)
                file.write(m_writer.set_temperature(temp, wait, first_printing_extruder_id));
        } else {
            // Set temperatures of all the printing extruders.
            for (unsigned int tool_id : print.extruders()) {
                int temp = print.config().nozzle_temperature_initial_layer.get_at(tool_id);
                if (print.config().ooze_prevention.value) {
                    if (print.config().idle_temperature.get_at(tool_id) == 0)
                        temp += print.config().standby_temperature_delta.value;
                    else
                        temp = print.config().idle_temperature.get_at(tool_id);
                }
                if (temp > 0)
                    file.write(m_writer.set_temperature(temp, wait, tool_id));
            }
        }
    }
}

inline GCode::ObjectByExtruder& object_by_extruder(
    std::map<unsigned int, std::vector<GCode::ObjectByExtruder>> &by_extruder,
    unsigned int                                                  extruder_id,
    size_t                                                        object_idx,
    size_t                                                        num_objects)
{
    std::vector<GCode::ObjectByExtruder> &objects_by_extruder = by_extruder[extruder_id];
    if (objects_by_extruder.empty())
        objects_by_extruder.assign(num_objects, GCode::ObjectByExtruder());
    return objects_by_extruder[object_idx];
}

inline std::vector<GCode::ObjectByExtruder::Island>& object_islands_by_extruder(
    std::map<unsigned int, std::vector<GCode::ObjectByExtruder>>  &by_extruder,
    unsigned int                                                   extruder_id,
    size_t                                                         object_idx,
    size_t                                                         num_objects,
    size_t                                                         num_islands)
{
    std::vector<GCode::ObjectByExtruder::Island> &islands = object_by_extruder(by_extruder, extruder_id, object_idx, num_objects).islands;
    if (islands.empty())
        islands.assign(num_islands, GCode::ObjectByExtruder::Island());
    return islands;
}

std::vector<GCode::InstanceToPrint> GCode::sort_print_object_instances(
    std::vector<GCode::ObjectByExtruder> 		&objects_by_extruder,
    const std::vector<LayerToPrint> 			&layers,
    // Ordering must be defined for normal (non-sequential print).
    const std::vector<const PrintInstance*> 	*ordering,
    // For sequential print, the instance of the object to be printing has to be defined.
    const size_t                     		 	 single_object_instance_idx)
{
    std::vector<InstanceToPrint> out;

    if (ordering == nullptr) {
        // Sequential print, single object is being printed.
        for (ObjectByExtruder &object_by_extruder : objects_by_extruder) {
            const size_t       layer_id     = &object_by_extruder - objects_by_extruder.data();
            //BBS:add the support of shared print object
            const PrintObject *print_object = layers[layer_id].original_object;
            //const PrintObject *print_object = layers[layer_id].object();
            if (print_object)
                out.emplace_back(object_by_extruder, layer_id, *print_object, single_object_instance_idx, print_object->instances()[single_object_instance_idx].model_instance->get_labeled_id());
        }
    } else {
        // Create mapping from PrintObject* to ObjectByExtruder*.
        std::vector<std::pair<const PrintObject*, ObjectByExtruder*>> sorted;
        sorted.reserve(objects_by_extruder.size());
        for (ObjectByExtruder &object_by_extruder : objects_by_extruder) {
            const size_t       layer_id     = &object_by_extruder - objects_by_extruder.data();
            //BBS:add the support of shared print object
            const PrintObject *print_object = layers[layer_id].original_object;
            //const PrintObject *print_object = layers[layer_id].object();
            if (print_object)
                sorted.emplace_back(print_object, &object_by_extruder);
        }
        std::sort(sorted.begin(), sorted.end());

        if (! sorted.empty()) {
            out.reserve(sorted.size());
            for (const PrintInstance *instance : *ordering) {
                const PrintObject &print_object = *instance->print_object;
                //BBS:add the support of shared print object
                //const PrintObject* print_obj_ptr = &print_object;
                //if (print_object.get_shared_object())
                //    print_obj_ptr = print_object.get_shared_object();
                std::pair<const PrintObject*, ObjectByExtruder*> key(&print_object, nullptr);
                auto it = std::lower_bound(sorted.begin(), sorted.end(), key);
                if (it != sorted.end() && it->first == &print_object)
                    // ObjectByExtruder for this PrintObject was found.
                    out.emplace_back(*it->second, it->second - objects_by_extruder.data(), print_object, instance - print_object.instances().data(), instance->model_instance->get_labeled_id());
            }
        }
    }
    return out;
}

namespace ProcessLayer
{

    static std::string emit_custom_gcode_per_print_z(
        GCode                                                   &gcodegen,
        const CustomGCode::Item 								*custom_gcode,
        unsigned int                                             current_extruder_id,
        // ID of the first extruder printing this layer.
        unsigned int                                             first_extruder_id,
        const PrintConfig                                       &config)
    {
        std::string gcode;
        // BBS
        bool single_filament_print = config.filament_diameter.size() == 1;

        if (custom_gcode != nullptr) {
            // Extruder switches are processed by LayerTools, they should be filtered out.
            assert(custom_gcode->type != CustomGCode::ToolChange);

            CustomGCode::Type   gcode_type = custom_gcode->type;
            bool  				color_change = gcode_type == CustomGCode::ColorChange;
            bool 				tool_change = gcode_type == CustomGCode::ToolChange;
            // Tool Change is applied as Color Change for a single extruder printer only.
            assert(!tool_change || single_filament_print);

            std::string pause_print_msg;
            int m600_extruder_before_layer = -1;
            if (color_change && custom_gcode->extruder > 0)
                m600_extruder_before_layer = custom_gcode->extruder - 1;
            else if (gcode_type == CustomGCode::PausePrint)
                pause_print_msg = custom_gcode->extra;
            //BBS: inserting color gcode is removed
#if 0
            // we should add or not colorprint_change in respect to nozzle_diameter count instead of really used extruders count
            if (color_change || tool_change)
            {
                assert(m600_extruder_before_layer >= 0);
                // Color Change or Tool Change as Color Change.
                // add tag for processor
                gcode += ";" + GCodeProcessor::reserved_tag(GCodeProcessor::ETags::Color_Change) + ",T" + std::to_string(m600_extruder_before_layer) + "," + custom_gcode->color + "\n";

                if (!single_filament_print && m600_extruder_before_layer >= 0 && first_extruder_id != (unsigned)m600_extruder_before_layer
                    // && !MMU1
                    ) {
                    //! FIXME_in_fw show message during print pause
                    DynamicConfig cfg;
                    cfg.set_key_value("color_change_extruder", new ConfigOptionInt(m600_extruder_before_layer));
                    gcode += gcodegen.placeholder_parser_process("machine_pause_gcode", config.machine_pause_gcode, current_extruder_id, &cfg);
                    gcode += "\n";
                    gcode += "M117 Change filament for Extruder " + std::to_string(m600_extruder_before_layer) + "\n";
                }
                else {
                    gcode += gcodegen.placeholder_parser_process("color_change_gcode", config.color_change_gcode, current_extruder_id);
                    gcode += "\n";
                    //FIXME Tell G-code writer that M600 filled the extruder, thus the G-code writer shall reset the extruder to unretracted state after
                    // return from M600. Thus the G-code generated by the following line is ignored.
                    // see GH issue #6362
                    gcodegen.writer().unretract();
                }
            }
            else {
#endif
                if (gcode_type == CustomGCode::PausePrint) // Pause print
                {
                    // add tag for processor
                    gcode += ";" + GCodeProcessor::reserved_tag(GCodeProcessor::ETags::Pause_Print) + "\n";
                    //! FIXME_in_fw show message during print pause
                    //if (!pause_print_msg.empty())
                    //    gcode += "M117 " + pause_print_msg + "\n";
                    gcode += gcodegen.placeholder_parser_process("machine_pause_gcode", config.machine_pause_gcode, current_extruder_id) + "\n";
                }
                else {
                    // add tag for processor
                    gcode += ";" + GCodeProcessor::reserved_tag(GCodeProcessor::ETags::Custom_Code) + "\n";
                    if (gcode_type == CustomGCode::Template)    // Template Custom Gcode
                        gcode += gcodegen.placeholder_parser_process("template_custom_gcode", config.template_custom_gcode, current_extruder_id);
                    else                                        // custom Gcode
                        gcode += custom_gcode->extra;

                }
                gcode += "\n";
#if 0
            }
#endif
        }

        return gcode;
    }
} // namespace ProcessLayer

namespace Skirt {
    static void skirt_loops_per_extruder_all_printing(const Print &print, const ExtrusionEntityCollection &skirt, const LayerTools &layer_tools, std::map<unsigned int, std::pair<size_t, size_t>> &skirt_loops_per_extruder_out)
    {
        // Prime all extruders printing over the 1st layer over the skirt lines.
        size_t n_loops = skirt.entities.size();
        size_t n_tools = layer_tools.extruders.size();
        size_t lines_per_extruder = (n_loops + n_tools - 1) / n_tools;

        // BBS. Extrude skirt with first extruder if min_skirt_length is zero
        //ORCA: Always extrude skirt with first extruder, independantly of if the minimum skirt length is zero or not. The code below
        // is left as a placeholder for when a multiextruder support is implemented. Then we will need to extrude the skirt loops for each extruder.
        //const PrintConfig &config = print.config();
        //if (config.min_skirt_length.value < EPSILON) {
            skirt_loops_per_extruder_out[layer_tools.extruders.front()] = std::pair<size_t, size_t>(0, n_loops);
        //} else {
        //    for (size_t i = 0; i < n_loops; i += lines_per_extruder)
        //        skirt_loops_per_extruder_out[layer_tools.extruders[i / lines_per_extruder]] = std::pair<size_t, size_t>(i, std::min(i + lines_per_extruder, n_loops));
        //}
    }

    static std::map<unsigned int, std::pair<size_t, size_t>> make_skirt_loops_per_extruder_1st_layer(
        const Print             				&print,
        const ExtrusionEntityCollection &skirt,
        const LayerTools                		&layer_tools,
        // Heights (print_z) at which the skirt has already been extruded.
        std::vector<coordf_t>  			    	&skirt_done)
    {
        // Extrude skirt at the print_z of the raft layers and normal object layers
        // not at the print_z of the interlaced support material layers.
        std::map<unsigned int, std::pair<size_t, size_t>> skirt_loops_per_extruder_out;
        //For sequential print, the following test may fail when extruding the 2nd and other objects.
        // assert(skirt_done.empty());
        if (skirt_done.empty() && print.has_skirt() && ! skirt.entities.empty() && layer_tools.has_skirt) {
            skirt_loops_per_extruder_all_printing(print, skirt, layer_tools, skirt_loops_per_extruder_out);
            skirt_done.emplace_back(layer_tools.print_z);
        }
        return skirt_loops_per_extruder_out;
    }

    static std::map<unsigned int, std::pair<size_t, size_t>> make_skirt_loops_per_extruder_other_layers(
        const Print 							&print,
        const ExtrusionEntityCollection     &skirt,
        const LayerTools                		&layer_tools,
        // Heights (print_z) at which the skirt has already been extruded.
        std::vector<coordf_t>			    	&skirt_done)
    {
        // Extrude skirt at the print_z of the raft layers and normal object layers
        // not at the print_z of the interlaced support material layers.
        std::map<unsigned int, std::pair<size_t, size_t>> skirt_loops_per_extruder_out;
        if (print.has_skirt() && ! skirt.entities.empty() && layer_tools.has_skirt &&
            // Not enough skirt layers printed yet.
            //FIXME infinite or high skirt does not make sense for sequential print!
            (skirt_done.size() < (size_t)print.config().skirt_height.value || print.has_infinite_skirt())) {
            bool valid = ! skirt_done.empty() && skirt_done.back() < layer_tools.print_z - EPSILON;
            assert(valid);
            // This print_z has not been extruded yet (sequential print)
            // FIXME: The skirt_done should not be empty at this point. The check is a workaround
            if (valid) {
#if 0
                // Prime just the first printing extruder. This is original Slic3r's implementation.
                skirt_loops_per_extruder_out[layer_tools.extruders.front()] = std::pair<size_t, size_t>(0, print.config().skirt_loops.value);
#else
                // Prime all extruders planned for this layer, see
                skirt_loops_per_extruder_all_printing(print, skirt, layer_tools, skirt_loops_per_extruder_out);
#endif
                assert(!skirt_done.empty());
                skirt_done.emplace_back(layer_tools.print_z);
            }
        }
        return skirt_loops_per_extruder_out;
    }

    static Point find_start_point(ExtrusionLoop& loop, float start_angle) {
        coord_t min_x = std::numeric_limits<coord_t>::max();
        coord_t max_x = std::numeric_limits<coord_t>::min();
        coord_t min_y = min_x;
        coord_t max_y = max_x;

        Points pts;
        loop.collect_points(pts);
        for (Point pt: pts) {
            if (pt.x() < min_x)
                min_x = pt.x();
            else if (pt.x() > max_x)
                max_x = pt.x();
            if (pt.y() < min_y)
                min_y = pt.y();
            else if (pt.y() > max_y)
                max_y = pt.y();
        }

        Point center((min_x + max_x)/2., (min_y + max_y)/2.);
        double r       = center.distance_to(Point(min_x, min_y));
        double deg     = start_angle * PI / 180;
        double shift_x = r * std::cos(deg);
        double shift_y = r * std::sin(deg);
        return Point(center.x()+shift_x, center.y() + shift_y);
    }

} // namespace Skirt

// Orca: Klipper can't parse object names with spaces and other spetical characters
std::string sanitize_instance_name(const std::string& name) {
    // Replace sequences of non-word characters with an underscore
    std::string result = std::regex_replace(name, std::regex("[ !@#$%^&*()=+\\[\\]{};:\",']+"), "_");
    // Remove leading and trailing underscores
    if (!result.empty() && result.front() == '_') {
        result.erase(result.begin());
    }
    if (!result.empty() && result.back() == '_') {
        result.erase(result.end() - 1);
    }

    return result;
}

inline std::string get_instance_name(const PrintObject *object, size_t inst_id) {
    auto obj_name = sanitize_instance_name(object->model_object()->name);
    auto name = (boost::format("%1%_id_%2%_copy_%3%") % obj_name % object->get_id() % inst_id).str();
    return sanitize_instance_name(name);
}

inline std::string get_instance_name(const PrintObject *object, const PrintInstance &inst) {
    return get_instance_name(object, inst.id);
}

std::string GCode::generate_skirt(const Print &print,
        const ExtrusionEntityCollection &skirt,
        const Point& offset,
        const LayerTools &layer_tools,
        const Layer& layer,
        unsigned int extruder_id)
{
    
    bool first_layer = (layer.id() == 0 && abs(layer.bottom_z()) < EPSILON);
    std::string gcode;
    // Extrude skirt at the print_z of the raft layers and normal object layers
    // not at the print_z of the interlaced support material layers.
    // Map from extruder ID to <begin, end> index of skirt loops to be extruded with that extruder.
    std::map<unsigned int, std::pair<size_t, size_t>> skirt_loops_per_extruder;
    skirt_loops_per_extruder = first_layer ?
        Skirt::make_skirt_loops_per_extruder_1st_layer(print, skirt, layer_tools, m_skirt_done) :
        Skirt::make_skirt_loops_per_extruder_other_layers(print, skirt, layer_tools, m_skirt_done);

    if (auto loops_it = skirt_loops_per_extruder.find(extruder_id); loops_it != skirt_loops_per_extruder.end()) {
        const std::pair<size_t, size_t> loops = loops_it->second;
       
        set_origin(unscaled(offset));

        m_avoid_crossing_perimeters.use_external_mp();
        Flow layer_skirt_flow = print.skirt_flow().with_height(float(m_skirt_done.back() - (m_skirt_done.size() == 1 ? 0. : m_skirt_done[m_skirt_done.size() - 2])));
        double mm3_per_mm = layer_skirt_flow.mm3_per_mm();
        for (size_t i = first_layer ? loops.first : loops.second - 1; i < loops.second; ++i) {
            // Adjust flow according to this layer's layer height.
            ExtrusionLoop loop = *dynamic_cast<const ExtrusionLoop*>(skirt.entities[i]);
            for (ExtrusionPath &path : loop.paths) {
                path.height = layer_skirt_flow.height();
                path.mm3_per_mm = mm3_per_mm;
            }

            //set skirt start point location
            if (first_layer && i==loops.first)
                this->set_last_pos(Skirt::find_start_point(loop, layer.object()->config().skirt_start_angle));

            //FIXME using the support_speed of the 1st object printed.
            gcode += this->extrude_loop(loop, "skirt", m_config.support_speed.value);
            if (!first_layer)
                break;
        }
        m_avoid_crossing_perimeters.use_external_mp(false);
        // Allow a straight travel move to the first object point if this is the first layer (but don't in next layers).
        if (first_layer && loops.first == 0)
            m_avoid_crossing_perimeters.disable_once();
    }
    return gcode;
}

// In sequential mode, process_layer is called once per each object and its copy,
// therefore layers will contain a single entry and single_object_instance_idx will point to the copy of the object.
// In non-sequential mode, process_layer is called per each print_z height with all object and support layers accumulated.
// For multi-material prints, this routine minimizes extruder switches by gathering extruder specific extrusion paths
// and performing the extruder specific extrusions together.
LayerResult GCode::process_layer(
    const Print                    			&print,
    // Set of object & print layers of the same PrintObject and with the same print_z.
    const std::vector<LayerToPrint> 		&layers,
    const LayerTools        		        &layer_tools,
    const bool                               last_layer,
    // Pairs of PrintObject index and its instance index.
    const std::vector<const PrintInstance*> *ordering,
    // If set to size_t(-1), then print all copies of all objects.
    // Otherwise print a single copy of a single object.
    const size_t                     		 single_object_instance_idx,
    // BBS
    const bool                               prime_extruder)
{
    assert(! layers.empty());
    // Either printing all copies of all objects, or just a single copy of a single object.
    assert(single_object_instance_idx == size_t(-1) || layers.size() == 1);

    // First object, support and raft layer, if available.
    const Layer         *object_layer  = nullptr;
    const SupportLayer  *support_layer = nullptr;
    const SupportLayer  *raft_layer    = nullptr;
    for (const LayerToPrint &l : layers) {
        if (l.object_layer && ! object_layer)
            object_layer = l.object_layer;
        if (l.support_layer) {
            if (! support_layer)
                support_layer = l.support_layer;
            if (! raft_layer && support_layer->id() < support_layer->object()->slicing_parameters().raft_layers())
                raft_layer = support_layer;
        }
    }

    const Layer* layer_ptr = nullptr;
    if (object_layer != nullptr)
        layer_ptr = object_layer;
    else if (support_layer != nullptr)
        layer_ptr = support_layer;
    const Layer& layer = *layer_ptr;
    LayerResult   result { {}, layer.id(), false, last_layer };
    if (layer_tools.extruders.empty())
        // Nothing to extrude.
        return result;

    // Extract 1st object_layer and support_layer of this set of layers with an equal print_z.
    coordf_t             print_z       = layer.print_z;
    //BBS: using layer id to judge whether the layer is first layer is wrong. Because if the normal
    //support is attached above the object, and support layers has independent layer height, then the lowest support
    //interface layer id is 0.
    bool                 first_layer   = (layer.id() == 0 && abs(layer.bottom_z()) < EPSILON);
    m_writer.set_is_first_layer(first_layer);
    unsigned int         first_extruder_id = layer_tools.extruders.front();

    // Initialize config with the 1st object to be printed at this layer.
    m_config.apply(layer.object()->config(), true);

    // Check whether it is possible to apply the spiral vase logic for this layer.
    // Just a reminder: A spiral vase mode is allowed for a single object, single material print only.
    m_enable_loop_clipping = true;
    if (m_spiral_vase && layers.size() == 1 && support_layer == nullptr) {
        bool enable = (layer.id() > 0 || !print.has_brim()) && (layer.id() >= (size_t)print.config().skirt_height.value && ! print.has_infinite_skirt());
        if (enable) {
            for (const LayerRegion *layer_region : layer.regions())
                if (size_t(layer_region->region().config().bottom_shell_layers.value) > layer.id() ||
                    layer_region->perimeters.items_count() > 1u ||
                    layer_region->fills.items_count() > 0) {
                    enable = false;
                    break;
                }
        }
        result.spiral_vase_enable = enable;
        // If we're going to apply spiralvase to this layer, disable loop clipping.
        m_enable_loop_clipping = !enable;
    }

    std::string gcode;
    assert(is_decimal_separator_point()); // for the sprintfs

    // add tag for processor
    gcode += ";" + GCodeProcessor::reserved_tag(GCodeProcessor::ETags::Layer_Change) + "\n";
    // export layer z
    char buf[64];
    sprintf(buf, print.is_BBL_printer() ? "; Z_HEIGHT: %g\n" : ";Z:%g\n", print_z);
    gcode += buf;
    // export layer height
    float height = first_layer ? static_cast<float>(print_z) : static_cast<float>(print_z) - m_last_layer_z;
    sprintf(buf, ";%s%g\n", GCodeProcessor::reserved_tag(GCodeProcessor::ETags::Height).c_str(), height);
    gcode += buf;
    // update caches
    m_last_layer_z = static_cast<float>(print_z);
    m_max_layer_z  = std::max(m_max_layer_z, m_last_layer_z);
    m_last_height = height;

    // Set new layer - this will change Z and force a retraction if retract_when_changing_layer is enabled.
    if (! m_config.before_layer_change_gcode.value.empty()) {
        DynamicConfig config;
        config.set_key_value("layer_num",   new ConfigOptionInt(m_layer_index + 1));
        config.set_key_value("layer_z",     new ConfigOptionFloat(print_z));
        config.set_key_value("max_layer_z", new ConfigOptionFloat(m_max_layer_z));
        gcode += this->placeholder_parser_process("before_layer_change_gcode",
            print.config().before_layer_change_gcode.value, m_writer.extruder()->id(), &config)
            + "\n";
    }

    PrinterStructure printer_structure           = m_config.printer_structure.value;
    bool need_insert_timelapse_gcode_for_traditional = false;
    if (printer_structure == PrinterStructure::psI3 &&
        !m_spiral_vase &&
        (!m_wipe_tower || !m_wipe_tower->enable_timelapse_print()) &&
        print.config().print_sequence == PrintSequence::ByLayer) {
        need_insert_timelapse_gcode_for_traditional = true;
    }
    bool has_insert_timelapse_gcode = false;
    bool has_wipe_tower             = (layer_tools.has_wipe_tower && m_wipe_tower);

    auto insert_timelapse_gcode = [this, print_z, &print]() -> std::string {
        std::string gcode_res;
        if (!m_config.time_lapse_gcode.value.empty()) {
            DynamicConfig config;
            config.set_key_value("layer_num", new ConfigOptionInt(m_layer_index));
            config.set_key_value("layer_z", new ConfigOptionFloat(print_z));
            config.set_key_value("max_layer_z", new ConfigOptionFloat(m_max_layer_z));
            gcode_res = this->placeholder_parser_process("timelapse_gcode", print.config().time_lapse_gcode.value, m_writer.extruder()->id(), &config) + "\n";
        }
        return gcode_res;
    };

    // BBS: don't use lazy_raise when enable spiral vase
    gcode += this->change_layer(print_z);  // this will increase m_layer_index
    m_layer = &layer;
    m_object_layer_over_raft = false;
    if(is_BBL_Printer()){
        if (printer_structure == PrinterStructure::psI3 && !need_insert_timelapse_gcode_for_traditional && !m_spiral_vase && print.config().print_sequence == PrintSequence::ByLayer) {
            std::string timepals_gcode = insert_timelapse_gcode();
            gcode += timepals_gcode;
            m_writer.set_current_position_clear(false);
            //BBS: check whether custom gcode changes the z position. Update if changed
            double temp_z_after_timepals_gcode;
            if (GCodeProcessor::get_last_z_from_gcode(timepals_gcode, temp_z_after_timepals_gcode)) {
                Vec3d pos = m_writer.get_position();
                pos(2) = temp_z_after_timepals_gcode;
                m_writer.set_position(pos);
            }
        }
    } else {
        if (!m_config.time_lapse_gcode.value.empty()) {
            DynamicConfig config;
            config.set_key_value("layer_num", new ConfigOptionInt(m_layer_index));
            config.set_key_value("layer_z", new ConfigOptionFloat(print_z));
            config.set_key_value("max_layer_z", new ConfigOptionFloat(m_max_layer_z));
            gcode += this->placeholder_parser_process("timelapse_gcode", print.config().time_lapse_gcode.value, m_writer.extruder()->id(),
                                                      &config) +
                     "\n";
        }
    }
    if (! m_config.layer_change_gcode.value.empty()) {
        DynamicConfig config;
        config.set_key_value("layer_num", new ConfigOptionInt(m_layer_index));
        config.set_key_value("layer_z",   new ConfigOptionFloat(print_z));
        gcode += this->placeholder_parser_process("layer_change_gcode",
            print.config().layer_change_gcode.value, m_writer.extruder()->id(), &config)
            + "\n";
        config.set_key_value("max_layer_z", new ConfigOptionFloat(m_max_layer_z));
    }
    //BBS: set layer time fan speed after layer change gcode
    gcode += ";_SET_FAN_SPEED_CHANGING_LAYER\n";

    if (print.calib_mode() == CalibMode::Calib_PA_Tower) {
        gcode += writer().set_pressure_advance(print.calib_params().start + static_cast<int>(print_z) * print.calib_params().step);
    } else if (print.calib_mode() == CalibMode::Calib_Temp_Tower) {
        auto offset = static_cast<unsigned int>(print_z / 10.001) * 5;
        gcode += writer().set_temperature(print.calib_params().start - offset);
    } else if (print.calib_mode() == CalibMode::Calib_VFA_Tower) {
        auto _speed = print.calib_params().start + std::floor(print_z / 5.0) * print.calib_params().step;
        m_calib_config.set_key_value("outer_wall_speed", new ConfigOptionFloat(std::round(_speed)));
    } else if (print.calib_mode() == CalibMode::Calib_Vol_speed_Tower) {
        auto _speed = print.calib_params().start + print_z * print.calib_params().step;
        m_calib_config.set_key_value("outer_wall_speed", new ConfigOptionFloat(std::round(_speed)));
    }
    else if (print.calib_mode() == CalibMode::Calib_Retraction_tower) {
        auto _length = print.calib_params().start + std::floor(std::max(0.0,print_z-0.4)) * print.calib_params().step;
        DynamicConfig _cfg;
        _cfg.set_key_value("retraction_length", new ConfigOptionFloats{_length});
        writer().config.apply(_cfg);
        sprintf(buf, "; Calib_Retraction_tower: Z_HEIGHT: %g, length:%g\n", print_z, _length);
        gcode += buf;
    }

    //BBS
    if (first_layer) {
        // Orca: we don't need to optimize the Klipper as only set once
        if (m_config.default_acceleration.value > 0 && m_config.initial_layer_acceleration.value > 0) {
            gcode += m_writer.set_print_acceleration((unsigned int)floor(m_config.initial_layer_acceleration.value + 0.5));
        }

        if (m_config.default_jerk.value > 0 && m_config.initial_layer_jerk.value > 0) {
            gcode += m_writer.set_jerk_xy(m_config.initial_layer_jerk.value);
        }

    }

    if (! first_layer && ! m_second_layer_things_done) {
      if (print.is_BBL_printer()) {
        // BBS: open powerlost recovery
        {
          gcode += "; open powerlost recovery\n";
          gcode += "M1003 S1\n";
        }
        // BBS: open first layer inspection at second layer
        if (print.config().scan_first_layer.value) {
          // BBS: retract first to avoid droping when scan model
          gcode += this->retract();
          gcode += "M976 S1 P1 ; scan model before printing 2nd layer\n";
          gcode += "M400 P100\n";
          gcode += this->unretract();
        }
      }
      // Reset acceleration at sencond layer
      // Orca: only set once, don't need to call set_accel_and_jerk
      if (m_config.default_acceleration.value > 0 && m_config.initial_layer_acceleration.value > 0) {
        gcode += m_writer.set_print_acceleration((unsigned int) floor(m_config.default_acceleration.value + 0.5));
      }

      if (m_config.default_jerk.value > 0 && m_config.initial_layer_jerk.value > 0) {
        gcode += m_writer.set_jerk_xy(m_config.default_jerk.value);
      }

        // Transition from 1st to 2nd layer. Adjust nozzle temperatures as prescribed by the nozzle dependent
        // nozzle_temperature_initial_layer vs. temperature settings.
        for (const Extruder &extruder : m_writer.extruders()) {
            if ((print.config().single_extruder_multi_material.value || m_ooze_prevention.enable) &&
                extruder.id() != m_writer.extruder()->id())
                // In single extruder multi material mode, set the temperature for the current extruder only.
                continue;
            int temperature = print.config().nozzle_temperature.get_at(extruder.id());
            if (temperature > 0 && temperature != print.config().nozzle_temperature_initial_layer.get_at(extruder.id()))
                gcode += m_writer.set_temperature(temperature, false, extruder.id());
        }

