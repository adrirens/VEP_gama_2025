/**
* Name: team
* Based on the internal empty template. 
* Author: julien-rsbrg
* Tags: 
*/


model team

import "../../includes/computer_model.gaml"

import "./police_officer.gaml"

/* abstract species of police officers' team to represent the hierarchy of the police force */
species team skills:[moving]{	
	bool is_mobile <- P_team_is_mobile; 
	float movement_amplitude <- P_team_movement_amplitude*step; 
	float speed <- P_team_speed; 
	float officer_view_dist <- P_dmax;
	
	list<police_officer> members update: members select !dead(each);
	list<police_officer> members_dispatched update: members_dispatched select !dead(each);
	map<string,int> member_name_to_id;
	
	list<rioter> detected_violent_offenders update:detected_violent_offenders select !dead(each);
	/* store the violente offenders detected */
	reflex update_detected_violent_offenders {
		loop single_offender over:detected_violent_offenders{
			if ((members+members_dispatched) min_of (each distance_to single_offender)) > officer_view_dist {
				detected_violent_offenders <- detected_violent_offenders - [single_offender];
			}
		}		
	}
	
	
	list<point> order_locations;
	bool take_regular_shape <- P_team_take_regular_shape;
	float regular_shape_radius <- P_team_regular_shape_radius;
	bool take_line_formation_shape <- P_team_take_line_formation_shape;
	float avg_shoulder_length <- (P_m_max+P_m_min)/2/320.0;
	
	
	int n_members_to_keep <- P_team_n_members_to_keep;
	int n_members_per_arrest_team <- P_team_n_members_per_arrest_team;
	
	/* add a new member to the team */
	action receive_member(police_officer new_member){
		if !(new_member in members){
			add (new_member.name :: length(members+members_dispatched)) to:member_name_to_id;
			add new_member to: members;
		}
	}
	
	/* memorize new detected violent offenders */
	action receive_detected_violent_offenders(list<rioter> sent_violent_offenders){
		loop svo over: sent_violent_offenders {
			if !(svo in detected_violent_offenders) {
				add svo to: detected_violent_offenders;
			}
		}
	}
	
	/* send an arrest team of n_members_to_dispatch officers against arrest_target rioter */
	action dispatch_arrest_team(rioter arrest_target, int n_members_to_dispatch<-3){
		assert n_members_to_dispatch <= length(members);
		
		list<int> members_id;
		list<point> members_vector_to_target;
		loop i from:0 to:length(members)-1{
			add i to:members_id;
			ask computer {
				add get_vector_in_torus_optimization(myself.members[i].location,arrest_target.location) to: members_vector_to_target;
			}
		}
		list<float> members_dist_to_target <- members_vector_to_target accumulate norm(each);
		list<int> sorted_members_id <- members_id sort_by members_dist_to_target[each];
		
		list<police_officer> members_to_dispatch;
		loop i from:0 to:n_members_to_dispatch-1{
			members_to_dispatch <- members_to_dispatch + members[sorted_members_id[i]];
		}
		
		members <- members - members_to_dispatch;
		members_dispatched <- members_dispatched + members_to_dispatch;
		
		create arrest_team with:(
			arrest_target:arrest_target
		) returns:created_arrest_teams;
		
		loop mtd over: members_to_dispatch{
			ask mtd{
				do receive_arrest_order(
					new_arrest_team:created_arrest_teams[0], 
					new_position_arrest_team:self.location, 
					new_arrest_target:arrest_target
				);
			}
			ask created_arrest_teams[0]{
				do receive_member(mtd);
			}
		}	
	}
	
	/* reintegrate a police officer to the team */
	action return_member_from_arrest_team(police_officer returning_member){
		members_dispatched <- members_dispatched - returning_member;
		add returning_member to: members;
	}
	
	/* consider dispatching an arrest team if a violent offender is detected and enough agents are present */
	reflex consider_dispatching_arrest_team {
		if ((length(detected_violent_offenders) > 0) and (length(members)-n_members_per_arrest_team >= n_members_to_keep)) {
			list<int> offenders_id;
			list<float> offenders_dist_to_team;
			loop i from:0 to:length(detected_violent_offenders)-1{
				add i to:offenders_id;
				
				float dmin <- #max_float;
				loop single_member over:members {
					point vector_member_to_offender;
					ask computer {
						vector_member_to_offender <- get_vector_in_torus_optimization(single_member.location,myself.detected_violent_offenders[i].location);
					}
					float d <- norm(vector_member_to_offender);
					if d < dmin {
						dmin <- d;
					}
				}
				add dmin to: offenders_dist_to_team;
			}			
			list<int> sorted_offenders_id <- offenders_id sort_by offenders_dist_to_team[each];
			list<rioter> sorted_possible_arrest_targets <- sorted_offenders_id accumulate detected_violent_offenders[each];
			bool no_free_target_found <- true;
			int i_target;
			loop while: no_free_target_found and i_target < length(sorted_possible_arrest_targets) {
				bool is_free_target <- true;
				int i_arrest_team;
				loop while: is_free_target and i_arrest_team < length(arrest_team){
					ask arrest_team[i_arrest_team] {
						if self.arrest_target = sorted_possible_arrest_targets[i_target] {
							is_free_target <- false;
						}
					}
					i_arrest_team <- i_arrest_team + 1;
				}
				no_free_target_found <- !is_free_target;
				i_target <- i_target + 1;
			}
			
			if !no_free_target_found and (length(sorted_possible_arrest_targets)>0){
				assert (i_target-1) < length(sorted_possible_arrest_targets);
				assert (i_target-1) >= 0;
				do dispatch_arrest_team(arrest_target:sorted_possible_arrest_targets[i_target-1], n_members_to_dispatch:n_members_per_arrest_team);
			}
		}
	}
	
	/* update the regular polygon shape taken by the team  */
	action update_regular_shape {		
		int n_agents <- length(members);	
		assert n_agents > 0;
		
		ask computer {
			list<point> temp_order_locations <- create_regular_shape(n_agents,myself.regular_shape_radius); 
			myself.order_locations <- rotate(temp_order_locations,myself.heading,{0.0,0.0});
			myself.order_locations <- translate(myself.order_locations,myself.location);
		}
		shape<-polygon(order_locations);
	}
	
	
	list<geometry> visu_ray; // where the agents can see with obstacles' obstructions accounted for
	list<float> val_180_angles; // list of angles of the casted vision rays at 180 degrees
	float disc_factor <- P_disc_factor;
	float half_dmax_lateral <- P_half_dmax_lateral;  
	float half_dmax_frontal <- P_half_dmax_frontal;
	
	init {
		int num <- int(180.0 / disc_factor);
		loop i from: 0 to: num {
			val_180_angles <<  ((i * disc_factor) - 180.0);
		}
		
	}
	
	/* return the distance before being */
	float f_circular(float alpha,float dmax_r) {
			geometry line;
			ask computer {
				line <- create_torus_multiline(myself.location, myself.location + ({cos(alpha), sin(alpha)} * dmax_r));
			}
		
			// geometry line <- line([location, location + ({cos(alpha), sin(alpha)} * dmax_r)]);
			list<wall> ws <- wall overlapping line;
			
			loop w over: ws {
				line <- line - w; // returns a multilinestring of segments of line deprived of the shape of w
				if line = nil {return 0.0;}
			}
			
			line <- line.geometries first_with (location in each.points); // only keep the segment where the agent is on
			if line = nil {
				return 0.0;
			}
			line <- line - self;
			if line = nil {
				return 0.0;
			}
			visu_ray << line;
			return line.perimeter;	// length of the line
		}
	
	/* update the formation to fill the predefined line */
	action update_line_formation_shape{		
		float dmin_lateral <- #max_float;
		visu_ray <- [];
		
		float h0 <- copy(heading);
		loop a over: val_180_angles {
			a <- a + h0;
			float d_a <- f_circular(a,half_dmax_lateral) + f_circular(a+180.0,half_dmax_lateral);
			
			if self = focus {
				write name + " alpha:" + a + " -- d_a:" + d_a;
			}
			if (d_a < dmin_lateral ) {
				dmin_lateral <- d_a;
				heading <- a + 90.0; // bias: should compute + or - 90.0
			}
		}
		
		float d_frontal <- f_circular(heading,half_dmax_frontal)+f_circular(heading+180.0,half_dmax_frontal);
				
		list<float> box_dimensions <- [dmin_lateral,d_frontal];
		ask computer {
			myself.order_locations <- optimize_fill(
				box_dimensions:box_dimensions, 
				n_elems:length(myself.members), 
				elem_dimensions:[myself.avg_shoulder_length,myself.avg_shoulder_length/2], 
				min_interspace_dimensions:[0.1,0.1]
			);
			point centroid <- compute_weighted_avg_points(myself.order_locations, myself.order_locations accumulate 1.0);
			myself.order_locations <- rotate(myself.order_locations,myself.heading-90.0, centroid);
			myself.order_locations <- translate(myself.order_locations,myself.location-centroid);
		}
	}
	
	/* receive a predefined shape of formation */
	action receive_formated_shape(list<point> sent_locations){
		assert length(sent_locations) >= length(members) label:'length(sent_locations) >= length(members):'+length(sent_locations)+ ">="+ length(members); // members
		order_locations <- sent_locations;
		take_regular_shape <- false;
		take_line_formation_shape <- false;
	}
	
	/* move the team randomly around */
	reflex wander {
		if (is_mobile){
			if (length(members)>0){
				float added_heading <- rnd(-movement_amplitude/2,movement_amplitude/2);
				heading<-heading+added_heading;
				point old_location <- copy(location);
				do move;
				
				point movement_vector <- location - old_location;
				if !(take_regular_shape or take_line_formation_shape){
					ask computer{
						point centroid <- compute_weighted_avg_points(myself.order_locations, myself.order_locations accumulate 1.0);
						myself.order_locations <- rotate(myself.order_locations,added_heading, centroid);
						myself.order_locations <- translate(myself.order_locations,movement_vector);
					}	
				}
			} else {
				list<point> md_locations <- members_dispatched accumulate [each.location];
				ask computer{
					point centroid <- compute_weighted_avg_points(md_locations,md_locations accumulate 1.0);
					point movement_vector <- centroid - myself.location;
					myself.order_locations <- translate(myself.order_locations,movement_vector);
					myself.location <- centroid;
				}
			}
			
		}
	}
	
	/* update shape (either line or regular) */
	reflex update_shape{
		if length(members)>0{
			if take_regular_shape {
				do update_regular_shape;
			} else if take_line_formation_shape {
				do update_line_formation_shape;
			}
		}
	}
	
	/* send the ordered positions to team members */
	reflex send_new_positions{
		int n_agents <- length(members);
		
		if !(take_regular_shape or take_line_formation_shape) {
			loop single_member over:(members+members_dispatched){
				int id_member <- member_name_to_id[single_member.name];
					ask single_member{
						do receive_my_position_from_team(myself.order_locations[id_member]);
					}
				}
		} else {
			point centroid;
			ask computer{
				centroid <- compute_weighted_avg_points(myself.order_locations,myself.order_locations accumulate 1.0);
			}
			
			int id_member<-0;
			loop single_member over:(members){
				ask single_member{
					do receive_my_position_from_team(myself.order_locations[id_member]);
				}
				id_member<-id_member + 1;
			}
			
			loop single_member over:(members_dispatched){
				int id_member <- member_name_to_id[single_member.name];
				ask single_member{
					do receive_my_position_from_team(centroid);
				}
			}				
		}
	}
	
	/* forget all violent offenders */
	reflex forget_violent_offenders {
		detected_violent_offenders <- [];
	}
	
	aspect base {
		draw shape color: #grey;
	}
	
	aspect vertices {
		if display_field_vision {
			loop l over: visu_ray {
				draw l color: #black;
			}
		}
		
		loop vertex over:order_locations{
			draw circle(0.25#m) at:vertex color:#green;
		}
	}
}

