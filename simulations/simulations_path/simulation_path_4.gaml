/**
* Name: simulationsquare
* Based on the internal empty template. 
* Author: julien-rsbrg
* Tags: 
*/


model simulationpath

import "../../models/unanimate/building.gaml"
import "./../common_simulation.gaml"
import "../../models/protest_configuration/path.gaml"

global {
	string exp_id;
	string sim_id;
	
	init {
		write "global simulation_path "+name;
		
		P_state_to_events_to_emotions <- [
			"flock"::[
			    "spatial_incursion"::["fear"],
			    "outnumbered"::["fear"],
			    "feeling_target_for_arrest"::["fear_confirmed","anger"],
			    "being_arrested"::["fear_confirmed","anger"],
			    //"unjust_arrest_around"::["anger"],
			    "surrounded"::["fear"]
			    //"any_police_officer_around"::[]
			    //"order_to_scatter_signal"::["fear"]
			],
			"violent"::[
				"spatial_incursion"::["fear"],
			    "outnumbered"::["fear"],
			    "feeling_target_for_arrest"::["fear"],
			    "being_arrested"::["fear_confirmed"],
			    //"unjust_arrest_around"::["anger"],
			    "surrounded"::["fear"]
			    //"any_police_officer_around"::["fear"]
			    //"order_to_scatter_signal"::["fear"]
			],
			"retreat"::[
				"spatial_incursion"::["fear"],
			    "outnumbered"::["fear"],
			    "feeling_target_for_arrest"::["fear_confirmed","anger"],
			    "being_arrested"::["fear_confirmed","anger"],
			    //"unjust_arrest_around"::["anger"],
			    "surrounded"::["fear"]
			    //"any_police_officer_around"::[]
			    //"order_to_scatter_signal"::["fear"]
			]
		];
		
		create path_world_builder returns: world_builders;
		ask world_builders[0]{
			do build_world;
		}
		
		ask experiment {
			exp_id <- self.name;
			write "exp_id="+exp_id;
		}
		
		ask simulation {
			sim_id <- string(int(self));
			write "sim_id="+sim_id;
		}
		
		map<string,unknown> sent_config_params <- [
				"seed"::seed,
				"experiment_id"::exp_id,
				"building"::(building accumulate (each.name :: each.shape.points)),
				"is_torus"::is_torus,
				"environment_size"::environment_size,
				"step"::step,
				"P_state_to_events_to_emotions"::P_state_to_events_to_emotions,
				
				// SFM
				"P_m_min"::P_m_min,
				"P_m_max"::P_m_max,
				"P_v0_mean"::P_v0_mean,
				"P_v0_std"::P_v0_std,
				"P_teta0"::P_teta0,
				"P_disc_factor"::P_disc_factor,
				"P_tau"::P_tau,
				"P_dmax"::P_dmax,
				"P_k"::P_k,
				
				// police
				"P_arrest_dist"::P_arrest_dist,
				"P_dmax_my_position_team"::P_dmax_my_position_team,
				"P_police_resistance_init"::P_police_resistance_init,
				"P_team_is_mobile"::P_team_is_mobile,
				"P_team_movement_amplitude"::P_team_movement_amplitude,
				"P_team_speed"::P_team_speed,
				"P_team_take_regular_shape"::P_team_take_regular_shape,
				"P_team_regular_shape_radius"::P_team_regular_shape_radius,
				"P_team_take_line_formation_shape"::P_team_take_line_formation_shape,
				"P_team_n_members_to_keep"::P_team_n_members_to_keep,
				"P_team_n_members_per_arrest_team"::P_team_n_members_per_arrest_team,
				"P_half_dmax_lateral"::P_half_dmax_lateral,
				"P_half_dmax_frontal"::P_half_dmax_frontal,
				
				// rioter
				"P_flocking_charisma_min"::P_flocking_charisma_min,
				"P_flocking_charisma_max"::P_flocking_charisma_max,
				"P_flocking_dist_imitation"::P_flocking_dist_imitation,
				"P_flocking_dist_attraction"::P_flocking_dist_attraction,
				"P_flocking_dist_repulsion"::P_flocking_dist_repulsion, 
					
				"P_rioter_arrest_resistance_init"::P_rioter_arrest_resistance_init,
				"P_rioter_resistance_init"::P_rioter_resistance_init,
				"P_rioter_energy_init"::P_rioter_energy_init,
				"P_rioter_energy_minimum"::P_rioter_energy_minimum,
				"P_rioter_energy_attack_consumption"::P_rioter_energy_attack_consumption,
				"P_rioter_energy_retreat_consumption"::P_rioter_energy_retreat_consumption,
				
				"P_rioter_grievance_min"::P_rioter_grievance_min,
				"P_rioter_grievance_max"::P_rioter_grievance_max,
				"P_rioter_risk_aversion_min"::P_rioter_risk_aversion_min,
				"P_rioter_risk_aversion_max"::P_rioter_risk_aversion_max,
				"P_rioter_attack_threshold_min"::P_rioter_attack_threshold_min,
				"P_rioter_attack_threshold_max"::P_rioter_attack_threshold_max,
				"P_rioter_retreat_threshold_min"::P_rioter_retreat_threshold_min,
				"P_rioter_retreat_threshold_max"::P_rioter_retreat_threshold_max,
						
				"P_rioter_k_liking"::P_rioter_k_liking,
				"P_rioter_lifetime_triedRetreat"::P_rioter_lifetime_triedRetreat,
						
				"P_rioter_dist_spatial_incursion"::P_rioter_dist_spatial_incursion,
				"P_rioter_ratio_cop_over_rioter_outnumbered"::P_rioter_ratio_cop_over_rioter_outnumbered,
						
				"P_spatial_incursion_to_detect"::P_spatial_incursion_to_detect,
				"P_outnumbered_to_detect"::P_outnumbered_to_detect,
				"P_feeling_target_for_arrest_to_detect"::P_feeling_target_for_arrest_to_detect,
				"P_being_arrested_to_detect"::P_being_arrested_to_detect,
				"P_unjust_arrest_around_to_detect"::P_unjust_arrest_around_to_detect,
				"P_surround_to_detect"::P_surround_to_detect,
				"P_any_police_officer_around_to_detect"::P_any_police_officer_around_to_detect,
				"P_order_to_scatter_signal_to_detect"::P_order_to_scatter_signal_to_detect,
				
				// emotion
				"P_emotion_decay"::P_emotion_decay,
				"P_emotional_contagion_activated"::P_emotional_contagion_activated,
				"P_emotional_contagion_fear_confirmed_when_violent"::P_emotional_contagion_fear_confirmed_when_violent,
				"P_max_liking_influence_to_violence"::P_max_liking_influence_to_violence,
				"P_threshold_ratio_violence_to_neutral"::P_threshold_ratio_violence_to_neutral,
				"P_emotional_contagion_threshold"::P_emotional_contagion_threshold,
				
				// General protest configuration
				"P_use_damageable_items"::P_use_damageable_items,
				"P_duration_before_respawn_item"::P_duration_before_respawn_item,
				"P resistance init items"::P_resistance_init_items,
				
				// Square protest configuration 
				// Torrens : base 5% (50/1000), riot police 20% (200/1000), mass protest 1% (50/5000) 
				// crowd density : 1 person per m2, 2 people per m2, tester 3 pour voir la tête
				"P_nb_rioters"::P_nb_rioters,
				//"P_nb_police_officers"::P_nb_police_officers,
				
				// Kettling protest configuration
				"P_path_n_subroads"::P_path_n_subroads,
				"P_path_n_cops_per_subroad"::P_path_n_cops_per_subroad
			];
		
		write " = = = = = = = = = = = = = = = = = = = =";
		write "sent_config_params:";
		write " = = = = = = = = = = = = = = = = = = = =";
		write sent_config_params;
		create data_recorder {
			do receive_meta_data(sent_config_params,exp_id, string(sim_id));
			do save_config_params;
		}
	}
	
	reflex write_cycle {
			write "exp_id="+exp_id+" -- sim_id="+sim_id+" -- cycle:"+cycle+"-- previous duration (s):"+duration;
		}
}



experiment path_batch_4  type:batch repeat:6 until: ( cycle*step > 4*3600 ) {    
     // Pedestrian params
	parameter "min mass" var: P_m_min init:80.0#kg; // fixed (take avg for Moussaid), 67kg avg in Torrens
	parameter "max mass" var: P_m_max init:80.0#kg; // fixed (take avg)
	parameter "desired speed" var: P_v0_mean init:1.3#m/#s; // fixed (take avg) Moussaid, 0.8 m s−1 Chen, https://athleexplique.fr/quelle-est-la-vitesse-de-marche-moyenne-par-age-et-par-sexe/ => 1.1 m.s-1 and 1.8 m.s-1
	parameter "desired speed std" var: P_v0_std min:0.0#m/#s init:0.0#m/#s; 
	parameter "max angle of vision" var: P_teta0 init:90.0; // 90 degrees Moussaid (half amplitude), 60 for Torrens	
	parameter "discretisation factor for the vision angle" var: P_disc_factor init:10.0; // degree, fixed (not essential)
	parameter "reaction time" var: P_tau init:0.5#s; // 0.5m Moussaid
	parameter "distance of vision" var: P_dmax init:7.0#m; // 10m Moussaid (8.0#m implementation Taillandier), 7m Torrens
	parameter "repulsion strength" var: P_k init:1.0*10^3; // 1.0*10^3 Moussaid
		
	// Police parameters
	parameter "dist to arrest" var:P_arrest_dist init:0.5#m; // 2m Torrens, consider contact and force police to get close to, can change to emulate weapons
	parameter "dist to positis_ion team max" var:P_dmax_my_position_team init: 20.0#m; // !! view dist, could be divided by two or more
	parameter "P time before starting_arrest" var:P_time_before_starting_arrest init:0*60.0;
	parameter "initial resistance of officers" var:P_police_resistance_init init:1000.0; // unbreakable
	parameter "are teams mobile?" var: P_team_is_mobile init:false; // VARY depend on the protest configuration (kettling::false,square::true,path::false)
	parameter "movement amplitude of teams" var:P_team_movement_amplitude init:20.0 unit:'degree/second' ; // knows where it goes in square
	parameter "speed of teams" var: P_team_speed init:1.3#m/#s; // !! try with 1.3m.s-1, take enough time for officers to follow
	parameter "should teams take a regular shape?" var:P_team_take_regular_shape init:false; // fixed false, better to optimize
	parameter "radius of teams' regular shape" var: P_team_regular_shape_radius init:2#m; // fixed not important/unused
	parameter "should teams take a line formation shape?" var: P_team_take_line_formation_shape init:true; // fixed true / should be overridden for kettling
	parameter "Number of members a team should keep at all times" var: P_team_n_members_to_keep init:0;  // depend on the distance of dispatch authorized  but could be set to 0
	parameter "Number of members to dispatch for arrest" var: P_team_n_members_per_arrest_team init:3; // !! should change, forces the nbr of required officers for arrest => decrease nb arrest over time
	parameter "Half max lateral distance for line formation" var: P_half_dmax_lateral init:10#m; // !! should depend on protest config and nbr police officer
	parameter "Half max frontal distance for line formation" var: P_half_dmax_frontal init:2#m; // idem
	
		
	// Rioter parameters
	parameter "Min charisma of flocking agents" var: P_flocking_charisma_min init:0.0;
	parameter "Max charisma of flocking agents" var: P_flocking_charisma_max init:1.0; // fixed full range variations  
	parameter "Dist imitation for flocking agents" var: P_flocking_dist_imitation init:7#m; // idem P_dmax 
	parameter "Dist attraction for flocking agents" var: P_flocking_dist_attraction init:7#m; // idem P_dmax 
	parameter "Dist repulsion for flocking agents" var: P_flocking_dist_repulsion init:0.5#m; // safe space, social distance, distance personnelle : de 45 cm à 125 cm (Hall Les distances chez l'homme 1971) 
	
	parameter "Initial arrest resistance of rioters" var:P_rioter_arrest_resistance_init init:int(5*3/step); // 5 s for arrest with 3 police officers (Lemos) => with step = 0.1s, should be 3*10*5 = 150, could be higher to represent police officer taking the rioter away [!!! arrest target could easily escape, need to be fixed B_arrestAgainstMe != B_beingArrested != B_feelingBeingArrested!!!] 
	parameter "Initial rioter resistance" var: P_rioter_resistance_init init:10.0; // useless never used 
	parameter "Initial rioter energy" var: P_rioter_energy_init init:5*60/step; // To VARY = maximum damage per rioter + used for fleeing, can break 1 big object, depend on resistance objects (trash bin = 50.0 ie 5 s to break it on your own, street lamp/sculpture = 6000.0 ie 10min to break it on your own => rnd uniform 1-5 min to break) 
	parameter "Minimum rioter energy to take actions" var: P_rioter_energy_minimum init:0.0; // fixed keep 0.0 (fine, the amplitude is what is interesting)
	parameter "Rioter energy consumption per attack" var: P_rioter_energy_attack_consumption init:1.0; // fixed
	parameter "Rioter energy consumption when retreating" var: P_rioter_energy_retreat_consumption init:1.0; // fixed can run 5 min with full energy = energy_init/(5*60)

	parameter "Min grievance" var: P_rioter_grievance_min init:0.0; // To VARY
	parameter "Max grievance" var: P_rioter_grievance_max init:1.0; // To VARY
	parameter "Min risk aversion" var: P_rioter_risk_aversion_min init:0.0; // To VARY
	parameter "Max risk aversion" var: P_rioter_risk_aversion_max init:1.0; // To VARY
	parameter "Min attack threshold" var: P_rioter_attack_threshold_min init:1.0; // To VARY, average H(1-L) Epstein
	parameter "Max attack threshold" var: P_rioter_attack_threshold_max init:1.0; // To VARY, average H(1-L) Epstein
	parameter "Min retreat threshold" var: P_rioter_retreat_threshold_min init:0.7; // To VARY, average H(1-L) Epstein
	parameter "Max retreat threshold" var: P_rioter_retreat_threshold_max init:0.7; // To VARY, average H(1-L) Epstein
						
	parameter "Liking k param (time)" var: P_rioter_k_liking init:0.0017; // To TUNE OK, 1h tension before being divided by two when feeling fear and sadness from police officers
	parameter "Lifetime of triedRetreat belief" var: P_rioter_lifetime_triedRetreat init:int(5*60/step); // fixed 5 minutes, step=0.1 and 5*60/step=3000 
		
	parameter "Dist spatial incursion" var: P_rioter_dist_spatial_incursion init:1.2#m;  // distance sociale : de 120 cm à 360 cm (mode proche : de 120 cm à 210 cm, mode éloigné : de 210 cm à 360 cm)  (Hall Les distances chez l'homme 1971) 
	parameter "Outnumbered if ratio cop over rioter is > than..." var: P_rioter_ratio_cop_over_rioter_outnumbered init:3.0; // fixed Nassauer
		
	parameter "Shoul detect spatial_incursion" var: P_spatial_incursion_to_detect init:true; // fixed (useless as is, interesting emotion after)
	parameter "Shoul detect outnumbered_to_detect" var: P_outnumbered_to_detect init:true; // fixed (useless as is, interesting emotion after)
	parameter "Shoul detect feeling_target_for_arrest" var:P_feeling_target_for_arrest_to_detect init:true; // fixed (useless as is, interesting emotion after) 
	parameter "Shoul detect being_arrested" var:P_being_arrested_to_detect init:true; // fixed (useless as is, interesting emotion after) 
	parameter "Shoul detect unjust_arrest_around" var:P_unjust_arrest_around_to_detect init:false; // fixed (useless as is, interesting emotion after)
	parameter "Shoul detect surround" var:P_surround_to_detect init:true; // fixed (useless as is, interesting emotion after)
	parameter "Shoul detect any_police_officer_around" var:P_any_police_officer_around_to_detect init:false; // fixed (useless as is, interesting emotion after)
	parameter "Shoul detect order_to_scatter_signal" var:P_order_to_scatter_signal_to_detect init:false; // fixed (useless as is, interesting emotion after)
	
	// (emotions)
	parameter "Emotion decay" var: P_emotion_decay init:step/4; // should last 4s [TO CHECK DURATION]
	parameter "Emotional contagion activated" var: P_emotional_contagion_activated init:true; // TO VARY
	parameter "Emotional contagion_fear_confirmed_when_violent" var:P_emotional_contagion_fear_confirmed_when_violent init:false;
	parameter "Max police social liking decreace on inhibition" var:P_max_liking_influence_to_violence init:0.5; // TO VARY
	parameter "Ratio applied on inhibition to shift violent to neutral" var:P_threshold_ratio_violence_to_neutral init:0.5; // fixed for stability
	parameter "Emotional contagion threshold" var: P_emotional_contagion_threshold init: 0.25;
	
	// General protest configuration
	parameter "Use damageable items" var:P_use_damageable_items init:true;
	parameter "P duration before respawn item" var:P_duration_before_respawn_item init:5*60.0;
	parameter "P resistance init items" var:P_resistance_init_items init:3*1*60.0/step;
	
	// Square protest configuration 
	// Torrens : base 5% (50/1000), riot police 20% (200/1000), mass protest 1% (50/5000) 
	// crowd density : 1 person per m2, 2 people per m2, tester 3 pour voir la tête
	parameter "Nb rioters" var:P_nb_rioters init:200; // TO VARY, think about police officer - protester ratio
	//parameter "Nb police officers" var:P_nb_police_officers init:3; // TO VARY, think about police officer - protester ratio
	
	// Path protest configuration 
	parameter "Nb subroads" var:P_path_n_subroads init:2;
	parameter "Nb cops per subroad" var:P_path_n_cops_per_subroad init:12;
	
	init {
		write 'enter experiment init:'+name;
	}
}