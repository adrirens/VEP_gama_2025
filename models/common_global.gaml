/**
* Name: commonglobal
* Based on the internal empty template. 
* Author: julien-rsbrg
* Tags: 
*/


model commonglobal

import "./citizen/rioter.gaml"
import "./police_force/police_officer.gaml"

global {
	bool display_field_vision <- false ;
	agent focus;
	float step <- 1.0;
	
	// Pedestrian parameters
	float P_m_min ; 
	float P_m_max ;
	float P_v0_mean ; // desired speed
	float P_v0_std ; // desired speed
	float P_teta0 ; // max angle of vision //degrees
	float P_disc_factor ; // discretisation factor for the vision angle
	float P_tau ; // reaction time
	float P_dmax ; // distance of vision
	float P_k ; // repulsion strength
	
	// Police parameters
	float P_arrest_dist;
	float P_dmax_my_position_team;
	float P_time_before_starting_arrest;
	float P_police_resistance_init;
	bool P_team_is_mobile;
	float P_team_movement_amplitude;
	float P_team_speed;
	bool P_team_take_regular_shape; 
	float P_team_regular_shape_radius;  
	bool P_team_take_line_formation_shape; 
	int P_team_n_members_to_keep; 
	int P_team_n_members_per_arrest_team;
	int P_arrest_team_n_min_members;
	float P_half_dmax_lateral;
	float P_half_dmax_frontal;
	
	// Rioter parameters
	
	float P_flocking_charisma_min;
	float P_flocking_charisma_max;
	float P_flocking_dist_imitation;
	float P_flocking_dist_attraction;
	float P_flocking_dist_repulsion;
	
	int P_rioter_arrest_resistance_init;
	float P_rioter_resistance_init; // <-10.0; 
    float P_rioter_energy_init; 
    float P_rioter_energy_minimum; 
    float P_rioter_energy_attack_consumption; 
    float P_rioter_energy_retreat_consumption; 
    
    //float P_rioter_perceived_hardship_min;
    //float P_rioter_perceived_hardship_max; 
	//float P_rioter_government_legitimacy_min;
	//float P_rioter_government_legitimacy_max; 
	float P_rioter_grievance_min;
    float P_rioter_grievance_max;
	float P_rioter_risk_aversion_min;
	float P_rioter_risk_aversion_max;
	float P_rioter_attack_threshold_min;
	float P_rioter_attack_threshold_max;
	float P_rioter_retreat_threshold_min;
	float P_rioter_retreat_threshold_max;
	
	float P_rioter_k_liking; // 1.0
	int P_rioter_lifetime_triedRetreat; // -1
	
	float P_rioter_dist_spatial_incursion; 
   	float P_rioter_ratio_cop_over_rioter_outnumbered; 
   	
   	bool P_spatial_incursion_to_detect;
	bool P_outnumbered_to_detect;
	bool P_feeling_target_for_arrest_to_detect;
	bool P_being_arrested_to_detect;
	bool P_unjust_arrest_around_to_detect;
	bool P_surround_to_detect;
	bool P_any_police_officer_around_to_detect;
	bool P_order_to_scatter_signal_to_detect;
	
	// emotion
	float P_emotion_decay;	
	bool P_emotional_contagion_activated;
	bool P_emotional_contagion_fear_confirmed_when_violent <- false;
	float P_max_liking_influence_to_violence;
	float P_threshold_ratio_violence_to_neutral;
	map<string,map<string,list<string>>> P_state_to_events_to_emotions;
	float P_emotional_contagion_threshold;
   	
   	// General protest configuration
   	bool P_use_damageable_items;
   	float P_duration_before_respawn_item;
   	float P_resistance_init_items;
   	
   	// Square protest configuration
   	int P_nb_rioters; // TO PARAMS	
	int P_nb_police_officers; // TO PARAMS
	
	// Path protest configuration
	int P_path_n_subroads;
	int P_path_n_cops_per_subroad;
	
	// Kettling protest configuration
	int P_kettling_n_ortho_cops;
	int P_kettling_n_transverse_cops;
	float P_kettling_dmax_cop_line_ortho;
	
	// GRID
	//int num_data <- 10 ;
	
	/*
	float grid_cell_width;
	float grid_cell_height;
	float grid_cell_range <- max(grid_cell_width,grid_cell_height);
	* 
	*/
}

species scheduler schedules: shuffle(rioter + police_officer) + team + arrest_team; // TODO: to turn fully asynchrone

/*
 * Abstract class to build the environment of the world where the moving agents will evolve
 */
species world_builder {
	action build_world {
		
	}
	
	list<point> items_locations;
	map<int,breakable_item> id_to_breakable_item;
	map<int,int> id_to_n_cycles_since_broken;
	float duration_before_respawn_item <- P_duration_before_respawn_item;
	
	action spawn_item (int id_item){
		create breakable_item with:(
			location:items_locations[id_item],
			resistance_init:P_resistance_init_items
		) returns:created_items;
		id_to_breakable_item[id_item] <- created_items[0];
		id_to_n_cycles_since_broken[id_item] <- 0;
	}
	
	reflex rebuild_destructed_items {
		loop i from:0 to:length(items_locations)-1{
			if P_use_damageable_items and dead(id_to_breakable_item[i]){
				id_to_n_cycles_since_broken[i] <- id_to_n_cycles_since_broken[i] + 1;
				if id_to_n_cycles_since_broken[i]*step > duration_before_respawn_item{
					do spawn_item(i);
				}
			}
		}
	}
}