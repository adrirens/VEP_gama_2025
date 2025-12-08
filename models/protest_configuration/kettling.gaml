/**
* Name: ketlling
* This wizard creates a new experiment file. 
* Author: julien-rsbrg
* Tags: 
*/

model ketlling

import "../citizen/rioter.gaml"
import "../police_force/police_officer.gaml"

global torus:false {
	bool is_torus <- false;
	float environment_size <- 50#m;
	geometry shape <- square(environment_size);
	geometry free_space <- copy(shape);
}

species kettling_world_builder parent:world_builder{
	int nb_rioters <- P_nb_rioters;
	//int nb_police_officers <- P_nb_police_officers;
	
	float path_size <- 20#m;
	
	int n_ortho_cops<-P_kettling_n_ortho_cops;
	int n_transverse_cops<-P_kettling_n_transverse_cops;
	
	float building_size <- (environment_size - path_size)/2;
	float dmax_cop_line_ortho <-P_kettling_dmax_cop_line_ortho;
	float ortho_cop_step<-dmax_cop_line_ortho/(n_ortho_cops+1);
	float transv_cop_step<-path_size/(n_transverse_cops+1);
	
	init { 
		items_locations <- [
				{building_size+path_size/4,environment_size/5},
				{environment_size-(building_size+path_size/4),environment_size*2/5},
				{environment_size/2,environment_size/2},
				{building_size+path_size/4,environment_size*3/5},
				{environment_size-(building_size+5),environment_size*4/5}
			];
	}
	
	
	action build_world {
		create computer with:(environment_size:environment_size);
		
		create building with:(L_vertices:[
					[0,0,0],
					[building_size,0,0],
					[building_size,environment_size,0],
					[0,environment_size,0]
				], max_anchor_dist:1#m);
		create building with:(L_vertices:[
					[environment_size-building_size,0,0],
					[environment_size,0,0],
					[environment_size,environment_size,0],
					[environment_size-building_size,environment_size,0]
				], max_anchor_dist:1#m);
				
		create wall with:(
			location:{environment_size/2,0},
			size:environment_size-2*building_size,
			transverse_angle:0,
			display_info:false,
			max_anchor_dist:1#m
		);
		create wall with:(
			location:{environment_size/2,environment_size},
			size:environment_size-2*building_size,
			transverse_angle:0,
			display_info:false,
			max_anchor_dist:1#m
		);
		
		ask building {
			free_space <- free_space - self.shape;
		}
		
		geometry riot_init_space<-polygon([
				{building_size,dmax_cop_line_ortho},
				{environment_size-building_size,dmax_cop_line_ortho},
				{environment_size-building_size,environment_size-dmax_cop_line_ortho},
				{building_size,environment_size-dmax_cop_line_ortho}
			]);
		create rioter number: nb_rioters with:(
			location:any_location_in(riot_init_space),
			free_space:free_space
		);
		
		// police officers
		
		
		list<point> sent_order_locations<-[];
		loop i_ortho_cop from:0 to:n_ortho_cops-1{
			loop j_transv_cop from:0 to:n_transverse_cops-1{
				float x_loc <- (j_transv_cop+1)*transv_cop_step;
				float y_loc <- (i_ortho_cop+1)*ortho_cop_step; 				
				add {x_loc,y_loc,0} to:sent_order_locations;
			}
		}
		
		//list<float> box_dimensions <- [path_size+1,P_half_dmax_frontal];
		//list<int> id_team_to_nb_officers <- [nb_police_officers div 2,nb_police_officers-(nb_police_officers div 2)];
		list<int> id_team_to_nb_officers <- [n_transverse_cops*n_ortho_cops,n_transverse_cops*n_ortho_cops];
		loop i_team over:[0,1]{
			create team with:(location:{environment_size/2,i_team*environment_size+(1-2*i_team)},heading:90.0) returns:created_team;
			
			point init_location <- {environment_size/2,i_team*environment_size+(1-2*i_team)};
			
			
			point centroid;
			
			ask computer {
				centroid <- compute_weighted_avg_points(sent_order_locations, sent_order_locations accumulate 1.0);
				sent_order_locations <- translate(sent_order_locations,created_team[0].location-centroid);
			}
			
			int id_cop <- 0;
			create police_officer number:id_team_to_nb_officers[i_team] with:(
				location:init_location, 
				is_torus:is_torus,
				my_team:created_team[0],
				free_space:free_space,
				detected_violent_offenders:[] //list(rioter) // TO REMOVE
				) returns:created_officers {
					location <- sent_order_locations[id_cop];
					id_cop <- id_cop + 1;
				}
			
			/* NOT OPTIMAL
			ask computer {
				write "length(created_officers) comp:"+length(created_officers);
				sent_order_locations <- optimize_fill(
					box_dimensions:box_dimensions, 
					n_elems:length(created_officers), 
					elem_dimensions:[created_team[0].avg_shoulder_length,created_team[0].avg_shoulder_length/2], 
					min_interspace_dimensions:[0.1,0.1]
				);
				write "sent_order_locations comp:"+sent_order_locations;
				centroid <- compute_weighted_avg_points(sent_order_locations, sent_order_locations accumulate 1.0);
				sent_order_locations <- translate(sent_order_locations,created_team[0].location-centroid);
			}
			* 
			*/
			
			
			write "sent_order_locations:"+sent_order_locations;
			write "created_team[0]:"+created_team[0];
			ask created_team[0]{
				loop single_officer over:created_officers{
					do receive_member(single_officer);
				}
				
				do receive_formated_shape(sent_order_locations);
			}
		}
		
		if P_use_damageable_items{
			loop i from:0 to:length(items_locations)-1{
				do spawn_item(i);
			}
		}
	}
}
