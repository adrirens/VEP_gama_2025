/**
* Name: square
* Based on the internal empty template. 
* Author: julien-rsbrg
* Tags: 
*/


model square

import "../../includes/computer_model.gaml"
import "../citizen/rioter.gaml"
import "../police_force/police_officer.gaml"


global torus:true {
	bool is_torus <- true;
	float environment_size <- 80#m; // more visible than a square of 241 x 241 m as square Charles-de-Gaulle
	geometry shape <- square(environment_size);
	geometry free_space <- copy(shape);
}

species square_world_builder parent:world_builder{
	int nb_rioters<-P_nb_rioters;
	int nb_police_officers<-P_nb_police_officers;
	
	init {
		items_locations <- [
				{environment_size/4,environment_size/4},
				{environment_size*3/4,environment_size/4},
				{environment_size/2,environment_size/2},
				{environment_size/4,environment_size*3/4},
				{environment_size*3/4,environment_size*3/4}
		];
	}
	
	action build_world {
		create computer with:(environment_size:environment_size);
		
		create rioter number: nb_rioters with:(free_space:free_space);
		
		point init_location <- {environment_size/2,environment_size/2};
		create team with:(location:init_location) returns:created_team;
		create police_officer number:nb_police_officers with:(
			location:init_location, 
			is_torus:is_torus,
			my_team:created_team[0],
			free_space:free_space,
			detected_violent_offenders:[] //list(rioter)
			) returns:created_officers;
	
		list<float> box_dimensions <- [P_half_dmax_lateral,P_half_dmax_frontal];
		list<point> sent_order_locations;
		ask computer {
			sent_order_locations <- optimize_fill(
				box_dimensions:box_dimensions, 
				n_elems:length(created_officers), 
				elem_dimensions:[created_team[0].avg_shoulder_length,created_team[0].avg_shoulder_length/2], 
				min_interspace_dimensions:[0.1,0.1]
			);
			point centroid <- compute_weighted_avg_points(sent_order_locations, sent_order_locations accumulate 1.0);
			sent_order_locations <- rotate(sent_order_locations,created_team[0].heading-90.0, centroid);
			sent_order_locations <- translate(sent_order_locations,created_team[0].location-centroid);
		}
		
		ask created_team[0]{
			loop single_officer over:created_officers{
				do receive_member(single_officer);
			}
			
			do receive_formated_shape(sent_order_locations);
		}
		
		if P_use_damageable_items{
			loop i from:0 to:length(items_locations)-1{
				do spawn_item(i);
			}
		}
	}
}


