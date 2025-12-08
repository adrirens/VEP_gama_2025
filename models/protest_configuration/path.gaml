/**
* Name: main
* This wizard creates a new experiment file. 
* Author: julien-rsbrg
* Tags: 
*/

model path

import "../citizen/rioter.gaml"
import "../unanimate/building.gaml"


global torus:true {
	bool is_torus <- true;
	float environment_size <- 50#m;
	geometry shape <- square(environment_size);
	geometry officer_free_space <- copy(shape);
	geometry rioter_free_space;
}

species path_world_builder parent:world_builder{
	int nb_rioters<-P_nb_rioters;
	float path_size<-20.0;
	
	float subroad_size<-10.0;
	int n_subroads <- P_path_n_subroads;
	float building_size <- environment_size/2 - path_size/2;
	float subroad_cop_step_back <- 1#m;
		
	int n_cops_per_subroad <- P_path_n_cops_per_subroad;
	
	init {
		items_locations <- [
				{environment_size/6,building_size+path_size/4},
				{environment_size*2/6,environment_size/2},
				{environment_size/2,building_size+path_size*3/4},
				{environment_size*4/6,environment_size/2},
				{environment_size*5/6,building_size+path_size/4}
		];
	}
	
	action build_world {
		create computer with:(environment_size:environment_size);
		
		geometry path_init <- polygon([
			{0,(environment_size-path_size)/2},
			{0,environment_size-(environment_size-path_size)/2},
			{environment_size,environment_size-(environment_size-path_size)/2},
			{environment_size,(environment_size-path_size)/2}
		]);
		
		list<point> anchors_locations;
		ask computer {
			 anchors_locations <- optimize_fill([environment_size,myself.path_size],30,[1,1],[1,1]);
			 point centroid <- compute_weighted_avg_points(anchors_locations, anchors_locations accumulate 1.0);
			 anchors_locations <- translate(anchors_locations,{environment_size/2,environment_size/2}-centroid);
		}
		write "anchors_locations:"+anchors_locations;
		loop i from: 0 to: length(anchors_locations)-1{
			create imitation_anchor with:(location:anchors_locations[i],heading:0,perception_dist:environment_size);	
		}
		
		
		float barrier_step_back <- 4#m;
		float barrier_size <- building_size-barrier_step_back;
		
		rioter_free_space <- polygon([
			{0,building_size-barrier_step_back/2},
			{environment_size,building_size-barrier_step_back/2},
			{environment_size,environment_size-(building_size-barrier_step_back/2)},
			{0,environment_size-(building_size-barrier_step_back/2)}
		]);
		
		loop i from:0 to:1{
			loop j from:0 to:n_subroads-1{
				create building with:(L_vertices:[
					[j*environment_size/n_subroads+subroad_size/2,i*(environment_size-building_size),0],
					[j*environment_size/n_subroads+subroad_size/2,i*environment_size + (1-i)*building_size,0],
					[(j+1)*environment_size/n_subroads-subroad_size/2,i*environment_size + (1-i)*building_size,0],
					[(j+1)*environment_size/n_subroads-subroad_size/2,i*(environment_size-building_size),0]
				], max_anchor_dist:1#m);
				
				if j > 0 {
					create building with:(L_vertices:[
						[j*environment_size/n_subroads+subroad_size/2,i*(environment_size-barrier_size),0],
						[j*environment_size/n_subroads+subroad_size/2,i*environment_size + (1-i)*barrier_size,0],
						[j*environment_size/n_subroads-subroad_size/2,i*environment_size + (1-i)*barrier_size,0],
						[j*environment_size/n_subroads-subroad_size/2,i*(environment_size-barrier_size),0]
					], max_anchor_dist:1#m);
				}
			}
		}
		
		if n_subroads>0{
			loop i from:0 to:1{
				create building with:(L_vertices:[
					[subroad_size/2,i*(environment_size-barrier_size),0],
					[subroad_size/2,i*environment_size + (1-i)*barrier_size,0],
					[0,i*environment_size + (1-i)*barrier_size,0],
					[0,i*(environment_size-barrier_size),0]
				], max_anchor_dist:1#m);
				
				create building with:(L_vertices:[
					[environment_size,i*(environment_size-barrier_size),0],
					[environment_size,i*environment_size + (1-i)*barrier_size,0],
					[environment_size-subroad_size/2,i*environment_size + (1-i)*barrier_size,0],
					[environment_size-subroad_size/2,i*(environment_size-barrier_size),0]
				], max_anchor_dist:1#m);
			}
			
		}
		
		ask building {
			officer_free_space <- officer_free_space - self.shape;
			rioter_free_space <- rioter_free_space - self.shape;
		}
		
		create rioter number: nb_rioters with:(
			location:any_location_in(path_init),
			free_space:rioter_free_space
		);
		
		loop i from:0 to:1{
			loop j from:0 to:n_subroads-1{				
				point team_init_location <- {j*environment_size/n_subroads, i*environment_size+(1-2*i)*(building_size-subroad_cop_step_back)};
				create team with:(location:team_init_location,heading:i*180+90) returns:created_team;
				
				point cop_init_location <- {j*environment_size/n_subroads, i*environment_size+(1-2*i)*building_size/2};
				create police_officer number: P_path_n_cops_per_subroad with:(
							location:cop_init_location, 
							is_torus:is_torus,
							my_team:created_team[0],
							free_space:officer_free_space,
							detected_violent_offenders:[]//list(rioter)
						) returns:created_officers;
				
			
				list<float> box_dimensions <- [subroad_size,barrier_step_back];
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
			}
		}
		
		if P_use_damageable_items{
			loop i from:0 to:length(items_locations)-1{
				do spawn_item(i);
			}
		}
	}
}

/*
experiment main type:gui {
	
	float epstein_ripeness_index <- 0.0;
	reflex compute_ripeness_indices {
		if length(rioter) > 0{
			epstein_ripeness_index <- mean(rioter accumulate (each.grievance))/mean(rioter accumulate (each.risk_aversion))*length(rioter select (not has_desire_op(each,new_predicate("violent"))))/length(rioter);	
		} else {
			epstein_ripeness_index <- 0.0;
		}
	}
	
	output {
		display main_display type:2d antialias:false {
			//species imitation_anchor aspect: base;
			//species repulsion_anchor aspect: base;
			
			species team aspect:base transparency:0.5;
			species team aspect:vertices transparency:0.5;
			species arrest_team aspect:base transparency:0.5;
			
			species rioter aspect: base;
			species police_officer aspect: base;
			species wall aspect: base refresh:false;
			species building aspect:base refresh:false;
		}
		
		display state_display type:2d antialias:false {
			species rioter aspect: state;
			species police_officer aspect: base;
			
			species wall aspect: base refresh:false;
			species building aspect:base refresh:false;
		}
		
		display Population_information refresh: every(1#cycles)  type: 2d {
			chart "Rioter state evolution" type: series size: {1,0.5} position: {0, 0} {
				data "N violent" value: length(rioter select (has_desire_op(each,new_predicate("violent")))) color: #red;
				data "N retreat" value: length(rioter select (has_desire_op(each,new_predicate("retreat")))) color: #green;
				data "N arrests" value: nb_rioters - length(rioter) color: #blue;
			}
			
			chart "Rioter police liking evolution" type: series size: {1,0.5} position: {0, 0.5} {
				data "max aggregated police social liking" value: max(rioter accumulate (each.aggregated_police_social_liking)) color: #green;
				data "avg aggregated police social liking" value: mean(rioter accumulate (each.aggregated_police_social_liking)) color: #blue;
				data "min aggregated police social liking" value: min(rioter accumulate (each.aggregated_police_social_liking)) color: #red;
			}
		}
		
		display Ripeness refresh: every(1#cycles) type: 2d {
			chart "Ripeness" type: series size: {1,0.5} position: {0, 0.5} {
				data "Epstein ripeness index" value: epstein_ripeness_index color: #green;
			}
		}
		
		
		display local_speed type:2d antialias:false{
			species local_indicator aspect: speed_val;
		}
		
		display local_compression type:2d antialias:false{
			species local_indicator aspect: compression_val;			
		}
		
		
		display local_N_violent type:2d antialias:false{
			species local_indicator aspect: N_violent_val;			
		}
		
	}
}
*/
