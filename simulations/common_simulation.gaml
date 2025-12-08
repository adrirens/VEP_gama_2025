/**
* Name: commonglobal
* Based on the internal empty template. 
* Author: julien-rsbrg
* Tags: 
*/


model commonsimulation

import "../models/citizen/rioter.gaml"
import "../models/police_force/police_officer.gaml"

global {
	init {
		write "global common simulation called";
	}
	
}

species metrics_handler { // mirrors:data_recorder
	float epstein_ripeness_index <- 0.0;
	float epstein_ripeness_index_with_emotion <- 0.0;
	
	int n_rioter update:length(rioter);
	float mean_grievance update:n_rioter>0 ? mean(rioter accumulate (each.grievance)):0.0;
	float mean_risk_aversion update:n_rioter>0 ? mean(rioter accumulate (each.risk_aversion)):0.0;
	float ratio_violent update:n_rioter>0 ? length(rioter select (not has_desire_op(each,new_predicate("violent"))))/n_rioter:0.0;
	float mean_aggr_police_social_liking update:n_rioter>0 ? mean(rioter accumulate (each.aggregated_police_social_liking)):0.0;
	
	reflex compute_ripeness_indices {
		if length(rioter) > 0{
			epstein_ripeness_index <- ratio_violent*mean_grievance/mean_risk_aversion;	
			epstein_ripeness_index_with_emotion <- epstein_ripeness_index * mean_aggr_police_social_liking;
		} else {
			epstein_ripeness_index <- 0.0;
			epstein_ripeness_index_with_emotion <- 0.0;
		}
	}
	
	int n_breakable_item update:length(breakable_item);
	int n_police_officer update:length(police_officer);
	int n_arrest_team update:length(arrest_team);
}

species data_recorder {
	map<string,unknown> config_params; // TO GIVE
	
	string start_date <- string(#now, 'yyyy-MM-dd_hh-mm-ss');
	string dest_folder;
	string machine_time;
	
	list rioter_cycles;
	list rioter_times; 
	list rioter_names;
	list rioter_x_locs;
	list rioter_y_locs;
	list rioter_is_in_state_flock;
	list rioter_is_in_state_violent;
	list rioter_is_in_state_retreat;
	list rioter_spatial_incursion_detected; 
	list rioter_outnumbered_detected; 
	list rioter_feeling_target_for_arrest_detected; 
	list rioter_being_arrested_detected; 
	list rioter_unjust_arrest_around_detected; 
	list rioter_surrounded_detected; 
	list rioter_any_police_officer_around_detected; 
	list rioter_order_to_scatter_signal_detected;
	list rioter_arrest_around_detected;
	list rioter_has_fear_confirmed;
	list rioter_has_fear;
	list rioter_has_anger;
	list rioter_has_sadness;
	list rioter_has_joy;
	list rioter_grievance;
	list rioter_arrest_proba;
	list rioter_aggr_police_social_liking;
	list rioter_record_damage_done;
	list rioter_risk_aversion;
	list rioter_police_social_liking_influence;
	list rioter_felt_negative_emotions;
	list rioter_feel_strong_negative_emotions;
	list rioter_current_energy;
	
	list police_cycles;
	list police_times; 
	list police_names;
	list police_x_locs;
	list police_y_locs;
	list police_is_in_state_formation; 
	list police_is_in_state_protect; 
	list police_is_in_state_retreat; 
	list police_n_detected_violent_offenders;
	list police_record_arrest_contribution;
	list police_resistance;
	
	list arrest_cycles;
	list arrest_times;
	list arrest_names;
	list arrest_x_locs;
	list arrest_y_locs;
	list arrest_n_members;
	list arrest_target_names;
	
	list item_cycles;
	list item_times;
	list item_names;
	list item_x_locs;
	list item_y_locs;
	list item_current_resistance;
	
	list metrics_cycles;
	list metrics_times;
	list metrics_n_rioter;
	list metrics_mean_grievance;
	list metrics_mean_risk_aversion;
	list metrics_ratio_violent;
	list metrics_mean_aggr_police_social_liking;
	list metrics_epstein_ripeness;
	list metrics_epstein_ripeness_with_emotion;
	list metrics_n_breakable_item;
	list metrics_n_police_officer;
	list metrics_n_arrest_team;
	
	init {
		write "recorder "+name+" created at "+start_date ;
	}
	
	action receive_meta_data(map<string,unknown> sent_config_params, string experiment_id, string simulation_id){
		assert sent_config_params!=nil;
		
		config_params <- sent_config_params;
		
		dest_folder <- "./results/"+"experiment_"+experiment_id+"/"+start_date+"_simulation_"+simulation_id+"/raw_data";
		write name+" get dest_folder = "+dest_folder;
	}
	
	action save_config_params{
		assert dest_folder!=nil label: "receive_meta_data to call before";
		
		save config_params
				to: dest_folder+"/config_params.json"
				format: "json" 
				header: true;
	}
	
	reflex record_data {
		loop single_agent over: rioter select (!dead(each)){
			ask single_agent{
				add cycle to: myself.rioter_cycles;
				add time to: myself.rioter_times;
				add self.name to: myself.rioter_names;
				add self.location.x to: myself.rioter_x_locs;
				add self.location.y to: myself.rioter_y_locs;
				
				add self.is_in_state["flock"] to: myself.rioter_is_in_state_flock;
				add self.is_in_state["violent"] to: myself.rioter_is_in_state_violent;
				add self.is_in_state["retreat"] to: myself.rioter_is_in_state_retreat;
				
				add self.is_event_detected["spatial_incursion"] to:myself.rioter_spatial_incursion_detected;
				add self.is_event_detected["outnumbered"] to:myself.rioter_outnumbered_detected;
				add self.is_event_detected["feeling_target_for_arrest"] to:myself.rioter_feeling_target_for_arrest_detected;
				add self.is_event_detected["being_arrested"] to:myself.rioter_being_arrested_detected;
				add self.is_event_detected["unjust_arrest_around"] to:myself.rioter_unjust_arrest_around_detected;
				add self.is_event_detected["surrounded"] to:myself.rioter_surrounded_detected;
				add self.is_event_detected["any_police_officer_around"] to:myself.rioter_any_police_officer_around_detected;
				add self.is_event_detected["order_to_scatter_signal"] to:myself.rioter_order_to_scatter_signal_detected;
				add self.is_event_detected["arrest_around"] to:myself.rioter_arrest_around_detected;
				
				add self.has_emotion(new_emotion("fear_confirmed"))  to: myself.rioter_has_fear_confirmed;
				add self.has_emotion(new_emotion("fear")) to:myself.rioter_has_fear;
				add self.has_emotion(new_emotion("anger")) to:myself.rioter_has_anger;
				add self.has_emotion(new_emotion("sadness")) to:myself.rioter_has_sadness;
				add self.has_emotion(new_emotion("joy")) to:myself.rioter_has_joy;
				
				add self.grievance to:myself.rioter_grievance;
				add self.arrest_proba to:myself.rioter_arrest_proba;
				add self.aggregated_police_social_liking to:myself.rioter_aggr_police_social_liking;
				add self.record_damage_done to: myself.rioter_record_damage_done;
				add self.risk_aversion to:myself.rioter_risk_aversion;
				add compute_police_social_liking_influence() to: myself.rioter_police_social_liking_influence;
			
				add self.felt_negative_emotions to: myself.rioter_felt_negative_emotions;
				add self.compute_feel_strong_negative_emotions() to: myself.rioter_feel_strong_negative_emotions;
				add self.current_energy to: myself.rioter_current_energy;
			}
		}
		
		loop single_agent over: police_officer select (!dead(each)){
			ask single_agent{
				add cycle to: myself.police_cycles;
				add time to: myself.police_times;
				add self.name to: myself.police_names;
				add self.location.x to: myself.police_x_locs;
				add self.location.y to: myself.police_y_locs;
				
				add self.is_in_state["formation"] to: myself.police_is_in_state_formation;
				add self.is_in_state["protect"] to: myself.police_is_in_state_protect;
				add self.is_in_state["retreat"] to: myself.police_is_in_state_retreat;
				
				add length(self.detected_violent_offenders) to:myself.police_n_detected_violent_offenders;
				add self.record_arrest_contribution to:myself.police_record_arrest_contribution;
				add self.current_resistance to: myself.police_resistance;
			}
		}
		
		loop single_agent over: arrest_team select (!dead(each)){
			ask single_agent{
				add cycle to: myself.arrest_cycles;
				add time to: myself.arrest_times;
				add self.name to: myself.arrest_names;
				add self.location.x to: myself.arrest_x_locs;
				add self.location.y to: myself.arrest_y_locs;
				
				add length(self.members) to: myself.arrest_n_members;
				add self.arrest_target.name to: myself.arrest_target_names;
			}
		}
		
		loop single_item over: breakable_item select (!dead(each)){
			ask single_item{
				add cycle to: myself.item_cycles;
				add time to: myself.item_times;
				add self.name to: myself.item_names;
				add self.location.x to: myself.item_x_locs;
				add self.location.y to: myself.item_y_locs;
				add self.current_resistance to: myself.item_current_resistance;
			}
		}
	
		ask metrics_handler{
				add cycle to: myself.metrics_cycles;
				add time to: myself.metrics_times;
				add self.n_rioter to: myself.metrics_n_rioter;
				add self.mean_grievance to: myself.metrics_mean_grievance;
				add self.mean_risk_aversion to: myself.metrics_mean_risk_aversion;
				add self.ratio_violent to: myself.metrics_ratio_violent;
				add self.mean_aggr_police_social_liking to: myself.metrics_mean_aggr_police_social_liking;
				add self.epstein_ripeness_index to: myself.metrics_epstein_ripeness;
				add self.epstein_ripeness_index_with_emotion to: myself.metrics_epstein_ripeness_with_emotion;
				
				add self.n_breakable_item to:myself.metrics_n_breakable_item;
				add self.n_police_officer to:myself.metrics_n_police_officer;
				add self.n_arrest_team to:myself.metrics_n_arrest_team;
			}
	}
	
	reflex save_data {
		assert dest_folder!=nil label: "receive_meta_data to call before";
		
		if length(rioter_cycles) > 0 {
			loop i from:0 to:length(rioter_cycles)-1 {
				//write "i/length(rioter_cycles):"+i+"/"+length(rioter_cycles);
				save [
				"species"::"rioter",
				"cycle"::rioter_cycles[i],
				"time"::rioter_times[i], 
				"name"::rioter_names[i],
				"x"::rioter_x_locs[i],
				"y"::rioter_y_locs[i],
				"state_flock"::rioter_is_in_state_flock[i],
				"state_violent"::rioter_is_in_state_violent[i],
				"state_retreat"::rioter_is_in_state_retreat[i],
				"spatial_incursion_detected"::rioter_spatial_incursion_detected[i],
				"outnumbered_detected"::rioter_outnumbered_detected[i],
				"feeling_target_for_arrest_detected"::rioter_feeling_target_for_arrest_detected[i], 
				"being_arrested_detected"::rioter_being_arrested_detected[i],
				"unjust_arrest_around_detected"::rioter_unjust_arrest_around_detected[i],
				"surrounded_detected"::rioter_surrounded_detected[i],
				"any_police_officer_around_detected"::rioter_any_police_officer_around_detected[i], 
				"order_to_scatter_signal_detected"::rioter_order_to_scatter_signal_detected[i],
				"arrest_around_detected"::rioter_arrest_around_detected[i],
				"has_fear_confirmed"::rioter_has_fear_confirmed[i],
				"has_fear"::rioter_has_fear[i],
				"has_anger"::rioter_has_anger[i],
				"has_sadness"::rioter_has_sadness[i],
				"has_joy"::rioter_has_joy[i],
				"grievance"::rioter_grievance[i],
				"arrest_proba"::rioter_arrest_proba[i],
				"aggr_police_social_liking"::rioter_aggr_police_social_liking[i],
				"record_damage_done"::rioter_record_damage_done[i],
				"risk_aversion"::rioter_risk_aversion[i],
				"police_social_liking_influence"::rioter_police_social_liking_influence[i],
				"felt_negative_emotions"::rioter_felt_negative_emotions[i],
				"feel_strong_negative_emotions"::rioter_feel_strong_negative_emotions[i],
				"current_energy"::rioter_current_energy[i]]
				to: dest_folder+"/data_cycle_"+cycle+"_rioter.csv" 
				format: "csv" 
				rewrite: false
				header: true;
			}
		}
		
		if length(police_cycles) > 0 {
			loop i from:0 to:length(police_cycles)-1 {
				//write "i/length(police_cycles):"+i+"/"+length(police_cycles);
				save [
					"species"::"police_officer",
					"cycle"::police_cycles[i],
					"time"::police_times[i],
					"name"::police_names[i],
					"x"::police_x_locs[i],
					"y"::police_y_locs[i],
					"state_formation"::police_is_in_state_formation[i], 
					"state_protect"::police_is_in_state_protect[i],
					"state_retreat"::police_is_in_state_retreat[i],
					"n_detected_violent_offenders"::police_n_detected_violent_offenders[i],
					"record_arrest_contribution"::police_record_arrest_contribution[i],
					"police_resistance"::police_resistance[i]
				]
				to: dest_folder+"/data_cycle_"+cycle+"_police_officer.csv" 
				format: "csv" 
				rewrite: false
				header: true;
			}
		}
		
		if length(arrest_cycles) > 0 {
			loop i from:0 to:length(arrest_cycles)-1 {
				//write "i/length(arrest_cycles):"+i+"/"+length(arrest_cycles);
				save [
					"species"::"arrest_team",
					"cycle"::arrest_cycles[i],
					"time"::arrest_times[i],
					"name"::arrest_names[i],
					"x"::arrest_x_locs[i],
					"y"::arrest_y_locs[i],
					"n_members"::arrest_n_members[i],
					"target_name"::arrest_target_names[i]
				]
				to: dest_folder+"/data_cycle_"+cycle+"_arrest.csv" 
				format: "csv" 
				rewrite: false
				header: true;
			}
		}
		
		if length(item_cycles) > 0 {
			loop i from:0 to:length(item_cycles)-1 {
				//write "i/length(item_cycles):"+i+"/"+length(item_cycles);
				save [
					"species"::"breakable_item",
					"cycle"::item_cycles[i],
					"time"::item_times[i],
					"name"::item_names[i],
					"x"::item_x_locs[i],
					"y"::item_y_locs[i],
					"current_resistance"::item_current_resistance[i]
				]
				to: dest_folder+"/data_cycle_"+cycle+"_item.csv" 
				format: "csv" 
				rewrite: false
				header: true;
			}
		}
		
		if length(metrics_cycles) > 0 {
			loop i from:0 to:length(metrics_cycles)-1 {
				//write "i/length(metrics_cycles):"+i+"/"+length(metrics_cycles);
				save [
					"species"::"metrics",
					"cycle"::metrics_cycles[i],
					"time"::metrics_times[i],
					"machine_time"::machine_time,
					"n_rioter"::metrics_n_rioter[i],
					"mean_grievance"::metrics_mean_grievance[i],
					"mean_risk_aversion"::metrics_mean_risk_aversion[i],
					"ratio_violent"::metrics_ratio_violent[i],
					"mean_aggr_police_social_liking"::metrics_mean_aggr_police_social_liking[i],
					"epstein_ripeness"::metrics_epstein_ripeness[i],
					"epstein_ripeness_with_emotion"::metrics_epstein_ripeness_with_emotion[i],
					"n_breakable_item"::metrics_n_breakable_item[i],
					"n_police_officer"::metrics_n_police_officer[i],
					"n_arrest_team"::metrics_n_arrest_team[i]
					  ]
					to: dest_folder+"/data_cycle_"+cycle+"_metrics.csv" 
					format: "csv" 
					rewrite: false
					header: true;
			}
		}
	}
	
	reflex flush_data {
		rioter_cycles <- [];
		rioter_times <- [];
		rioter_names <- [];
		rioter_x_locs <- [];
		rioter_y_locs <- [];
		rioter_is_in_state_flock <- [];
		rioter_is_in_state_violent <- [];
		rioter_is_in_state_retreat <- [];
		rioter_spatial_incursion_detected <- [];
		rioter_outnumbered_detected <- [];
		rioter_feeling_target_for_arrest_detected <- []; 
		rioter_being_arrested_detected <- []; 
		rioter_unjust_arrest_around_detected <- [];
		rioter_surrounded_detected <- [];
		rioter_any_police_officer_around_detected <- [];
		rioter_order_to_scatter_signal_detected <- [];
		rioter_arrest_around_detected <- [];
		rioter_has_fear_confirmed <- [];
		rioter_has_fear <- [];
		rioter_has_anger <- [];
		rioter_has_sadness <- [];
		rioter_has_joy <- [];
		rioter_grievance <- [];
		rioter_arrest_proba <- [];
		rioter_aggr_police_social_liking <- [];
		rioter_record_damage_done <- [];
		rioter_risk_aversion <- [];
		rioter_police_social_liking_influence <- [];
		rioter_felt_negative_emotions <- [];
		rioter_feel_strong_negative_emotions <- [];
		rioter_current_energy <- [];
		
		police_cycles <- [];
		police_times <- [];
		police_names <- [];
		police_x_locs <- [];
		police_y_locs <- [];
		police_is_in_state_formation <- [];
		police_is_in_state_protect <- [];
		police_is_in_state_retreat <- [];
		police_n_detected_violent_offenders <- [];
		police_record_arrest_contribution <- [];
		police_resistance <- [];
		
		arrest_cycles <- [];
		arrest_times <- [];
		arrest_names <- [];
		arrest_x_locs <- [];
		arrest_y_locs <- [];
		arrest_n_members <- [];
		arrest_target_names <- [];
		
		item_cycles <- [];
		item_times <- [];
		item_names <- [];
		item_x_locs <- [];
		item_y_locs <- [];
		item_current_resistance <- [];
		
		metrics_cycles <- [];
		metrics_times <- [];
		metrics_n_rioter <- [];
		metrics_mean_grievance <- [];
		metrics_mean_risk_aversion <- [];
		metrics_ratio_violent <- [];
		metrics_mean_aggr_police_social_liking <- [];
		metrics_epstein_ripeness <- [];
		metrics_epstein_ripeness_with_emotion <- [];
		metrics_n_breakable_item <- [];
		metrics_n_police_officer <- [];
		metrics_n_arrest_team <- [];
	}
	
}