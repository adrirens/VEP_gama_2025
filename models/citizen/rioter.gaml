/**
* Name: rioter
* Based on the internal empty template. 
* Author: julien-rsbrg
* Tags: 
*/


model rioter


import "../unanimate/items.gaml"
import "./base_pedestrian.gaml"
import "../police_force/police_officer.gaml"
import "../unanimate/items.gaml"
import "../common_global.gaml"

/*
 * species defining the rioter (with its BDI and state mechanisms)
 */
species rioter parent:boid control:simple_bdi{	
	
	////////////////////////// Flocking /////////////////////////////////////
	float m <- rnd(P_m_min,P_m_max);
	float shoulder_length <- m/320.0; 
	geometry _shape <- square(shoulder_length);
	float shape_angle <- 120.0;
	float size <- shoulder_length;
	unknown agents_flocking_with <- rioter;
	
	float speed <- gauss(P_v0_mean, P_v0_std); // TO GIVE
	rgb my_color <- #black;
	
	
	user_command focus {
		focus <- self;
	}
	
	/////////////////////////// BDI Architecture /////////////////////////////////////////
	
	// PARAMETERS
	float attack_dist<-5.0;
	
	bool use_emotions_architecture <- true;
    bool use_personality <- true;
    float extroversion <- rnd(1.0);
	float neurotism <- rnd(1.0);
	float charisma <- extroversion;
	float receptivity <- 1-neurotism;
    float conscientiousness <- 1.0; // Force to keep plans and intentions
    bool emotional_contagion_activated <- P_emotional_contagion_activated;
    float emotional_contagion_threshold <- P_emotional_contagion_threshold;
    
    int arrest_resistance_init <- P_rioter_arrest_resistance_init; // <- 10; 
    float resistance_init <- P_rioter_resistance_init; // <-10.0; 
    float energy_init <- P_rioter_energy_init; 
    float energy_minimum <- P_rioter_energy_minimum; 
    float energy_attack_consumption <- P_rioter_energy_attack_consumption; 
    float energy_retreat_consumption <- P_rioter_energy_retreat_consumption; 
    float current_energy <- energy_init;
    float record_damage_done;
    
	//float perceived_hardship <- rnd(P_rioter_perceived_hardship_min,P_rioter_perceived_hardship_max); 
	//float government_legitimacy <- rnd(P_rioter_government_legitimacy_min,P_rioter_government_legitimacy_max); 
	float grievance<-rnd(P_rioter_grievance_min,P_rioter_grievance_max);// perceived_hardship*(1-government_legitimacy);
	float risk_aversion <- rnd(P_rioter_risk_aversion_min,P_rioter_risk_aversion_max);
	float attack_threshold <- rnd(P_rioter_attack_threshold_min,P_rioter_attack_threshold_max);
	float retreat_threshold <- rnd(P_rioter_retreat_threshold_min,P_rioter_retreat_threshold_max);
	float arrest_proba;
	
	map<string,float> police_social_liking_with;
	float aggregated_police_social_liking;
	
	list possible_negative_emotions <- ["fear","sadness"];
	list possible_positive_emotions <- ["hope", "joy"];
	int N_possible_negative_emotions <- length(possible_negative_emotions);
	int N_possible_positive_emotions <- length(possible_positive_emotions);
	float felt_negative_emotions;
	
	float k_liking <- P_rioter_k_liking; // 1.0
	
	float max_liking_influence_to_violence <- P_max_liking_influence_to_violence;
	float threshold_ratio_violence_to_neutral <- P_threshold_ratio_violence_to_neutral;
	
	int lifetime_triedRetreat <- P_rioter_lifetime_triedRetreat;
		
	// (specifically) BELIEFS
	breakable_item victim_target<-nil update:(dead(victim_target))? nil:victim_target;
	// safe (only by keyword)
	
	// (specifically) INTENTIONS
	// flock, violent (attackVictimTarget, defineVictimTarget), retreat
	predicate defineVictimTarget <- new_predicate("defineVictimTarget");
		
	
	/// /// /// /// PERCEPTION/RULES /// /// /// ///
	list<police_officer> seen_police_officers update: police_officer at_distance view_dist;
	int N_police_officers_around update: length(seen_police_officers);
	//int N_active_around;
	int N_violent_around;
	list<rioter> rioters_around update:rioter at_distance view_dist;
	
	reflex perceive_locationPotentialVictim {
		list<agent> perceived_breakable_items <- ((agents of_generic_species breakable_item) - rioter) at_distance view_dist;
		loop single_item over: perceived_breakable_items{
			do add_belief(new_predicate("locationPotentialVictim",["location_value"::single_item.location],true,single_item),10.0,1);
		}		
	}
	
	/// /// Perception and Beliefs /// ///
	
    map<string,map<string,list<string>>> state_to_events_to_emotions <- P_state_to_events_to_emotions;
    list<string> authorized_states <- ["violent","retreat","flock"];
    list<string> authorized_emotions <- ["fear","anger","fear_confirmed"];
    
    init {
    	//write name+" state_to_events_to_emotions:"+state_to_events_to_emotions;
    }
    
    map<string,bool> is_event_to_detect <- [
	    "spatial_incursion"::P_spatial_incursion_to_detect,
	    "outnumbered"::P_outnumbered_to_detect,
	    "feeling_target_for_arrest"::P_feeling_target_for_arrest_to_detect,
	    "being_arrested"::P_being_arrested_to_detect,
	    "unjust_arrest_around"::P_unjust_arrest_around_to_detect,
	    "surrounded"::P_surround_to_detect,
	    "any_police_officer_around"::P_any_police_officer_around_to_detect,
	    "order_to_scatter_signal"::P_order_to_scatter_signal_to_detect,
	    "arrest_around"::true
    ];
    map<string,bool> is_event_detected <- copy(is_event_to_detect) update:convert_map_values_to_false(is_event_detected);
    
    map<unknown,bool> convert_map_values_to_false(map<unknown,bool> map_to_bool){
    	loop k over:map_to_bool.keys{
    		map_to_bool[k]<-false;
    	}
    	return map_to_bool;
    }
    
    float dist_spatial_incursion <- P_rioter_dist_spatial_incursion; // TO GIVE
   	
   	float ratio_cop_over_rioter_outnumbered <- P_rioter_ratio_cop_over_rioter_outnumbered; // TO GIVE
   	
   	list<arrest_team> seen_arrest_teams update: arrest_team at_distance view_dist;
   	
   	bool received_arrest_process;
   	arrest_team arrest_team_arresting_me;
   	
   	
   	list<rioter> detected_violent_offenders update: detected_violent_offenders at_distance view_dist;
   	
   	/* check the presence of violent offenders around */
   	action receive_violent_offender(rioter violent_offender){
   		//write "4 - ";   		
   		if !(self.detected_violent_offenders contains violent_offender){
   			//write "5 - violent_offender, detected_violent_offenders = "+violent_offender+", "+detected_violent_offenders;
   			detected_violent_offenders <- detected_violent_offenders + [violent_offender];
   			//write "5 - passed";
   		}
   		//write "4 - passed";
   	}
   	
   	   
   	list<police_officer> received_order_to_scatter_signals;
   	
   	/* message reception from police officer to scatter */
   	action receive_order_to_scatter(police_officer sender_order_to_scatter){
   		add sender_order_to_scatter to: received_order_to_scatter_signals;
   	}
   	
   	/// /// list of emotional triggers /// ///
   	
   	/* check spatial incursion with police officers */
   	action check_spatial_incursion {
   		police_officer closest_officer <- seen_police_officers closest_to self;
   		if closest_officer != nil {
   			is_event_detected["spatial_incursion"] <-  (
	   			closest_officer distance_to self < dist_spatial_incursion
	   		);
   		} else {
   			is_event_detected["spatial_incursion"] <- false;
   		}
   		
   		
   		if is_event_detected["spatial_incursion"] {
			loop single_officer over: (seen_police_officers at_distance dist_spatial_incursion){
				do add_belief(new_predicate("spatial_incursion",single_officer),1.0,1);
			}
		} else {
			do add_belief(new_predicate("spatial_incursion",false),1.0,1);
		}
   	}
   	
   	/* check rioters are currently outnumbered by police officers around the agent */
   	action check_outnumbered {
   		int N_rioters_around <- length(rioters_around)+1;
   		is_event_detected["outnumbered"] <- (
   			N_police_officers_around/N_rioters_around > ratio_cop_over_rioter_outnumbered
   		);
   		
   		if is_event_detected["outnumbered"]{
			loop single_officer over: seen_police_officers{
				do add_belief(new_predicate(
					"outnumbered",
					single_officer			
				),1.0,1);
			}
		} else {
			do add_belief(new_predicate("outnumbered",false),1.0,1);
		}
   	}
   	
   	/* check an arrest is going on around */
   	action check_arrest_around{
   		is_event_detected["arrest_around"] <- !empty(seen_arrest_teams);
   		
   		if is_event_detected["arrest_around"]{
			loop single_arrest_team over: seen_arrest_teams{
				do add_belief(new_predicate(
					"arrest_around",
					single_arrest_team		
				),1.0,1);
			}
		} else {
			do add_belief(new_predicate("arrest_around",false),1.0,1);
		}
   	}
   	
   	/* check an arrest seems directed to the agent */
   	action check_feeling_target_for_arrest{
   		int i_arrest_team;
		int n_seen_arrest_team <- length(seen_arrest_teams);
		loop while: i_arrest_team < n_seen_arrest_team and !is_event_detected["feeling_target_for_arrest"] {
   			if seen_arrest_teams[i_arrest_team].to_target_cone overlaps self {
   				is_event_detected["feeling_target_for_arrest"] <- true;
   			}
   			i_arrest_team <- i_arrest_team + 1;
   		}
   		
   		if is_event_detected["feeling_target_for_arrest"] {
			loop single_officer over: seen_arrest_teams[i_arrest_team-1].members{
				do add_belief(
					new_predicate(
						"feeling_target_for_arrest",
						["arrest_target"::seen_arrest_teams[i_arrest_team-1].arrest_target,
						 "arrest_team"::seen_arrest_teams[i_arrest_team-1]],
						single_officer
				),1.0,1);
			}
		} else {
			do add_belief(new_predicate("feeling_target_for_arrest",false),1.0,1);
		}
   	}
   	
   	/* check the agent is currently being arrested */
   	action check_being_arrested{	
   		arrest_team_arresting_me <- nil;
   		ask seen_arrest_teams {
   			if arrest_target = myself {
   				myself.is_event_detected["being_arrested"]<- true;
   				myself.arrest_team_arresting_me <- self;
   			}
   		}
   		
		if is_event_detected["being_arrested"] {
			loop single_officer over: arrest_team_arresting_me.members{
				do add_belief(new_predicate(
					"being_arrested",
					["arrest_team"::arrest_team_arresting_me],
					single_officer			
				),1.0,1);
			}
		} else {
			do add_belief(new_predicate("being_arrested",false),1.0,1);
		}
		
	}
	
	/* check an arrest is going around against a rioter that is thought innocent */
	action check_unjust_arrest_around{
		int i_arrest_team;
		int n_seen_arrest_team <- length(seen_arrest_teams);
		loop while: i_arrest_team < n_seen_arrest_team and !is_event_detected["unjust_arrest_around"] {
			if !(detected_violent_offenders contains seen_arrest_teams[i_arrest_team].arrest_target){
				is_event_detected["unjust_arrest_around"] <- true;	
			}
			i_arrest_team <- i_arrest_team + 1;
		}
		
		if is_event_detected["unjust_arrest_around"] {
			loop single_officer over: seen_arrest_teams[i_arrest_team-1].members{
				do add_belief(
					new_predicate(
						"unjust_arrest_around",
						["arrest_target"::seen_arrest_teams[i_arrest_team-1].arrest_target,
						 "arrest_team"::seen_arrest_teams[i_arrest_team-1]
						],
						single_officer
				),1.0,1);
			}
		} else {
			do add_belief(new_predicate("unjust_arrest_around",false),1.0,1);
		}
	}
   	
   	/* check being surrounded by walls or police officers */
   	action check_surrounded{
		ask computer  {
			myself.is_event_detected["surrounded"] <- is_surrounded(
				obstacles:list(police_officer),
				n_subdivisions_to_surround:3, 
				n_subdivisions:4, 
				origin_location:myself.location,
				perception_distance:myself.view_dist, 
				init_angle:rnd(360.0)
			);
		}
		if is_event_detected["surrounded"] {
			loop single_officer over: seen_police_officers{
				do add_belief(new_predicate("surrounded",single_officer),1.0,1);
			}
		} else {
			do add_belief(new_predicate("surrounded",false),1.0,1);
		}
	}
	
	/* check police officers are in vision range */
	action check_seen_police_officers{
		is_event_detected["any_police_officer_around"] <- !empty(seen_police_officers);
		
		if is_event_detected["any_police_officer_around"] {
			loop single_officer over: seen_police_officers{
				do add_belief(new_predicate("any_police_officer_around",single_officer),1.0,1);
			}
		} else {
			do add_belief(new_predicate("any_police_officer_around",false),1.0,1);
		}
	}
	
	/* check an order to scatter from the police officers has been heard by the agent */
	action check_order_to_scatter_signal{
		is_event_detected["order_to_scatter_signal"] <- !empty(received_order_to_scatter_signals);
		
		if is_event_detected["order_to_scatter_signal"] {
			loop single_officer over: received_order_to_scatter_signals{
				do add_belief(new_predicate("order_to_scatter_signal",single_officer),1.0,1);
			}
		} else {
			do add_belief(new_predicate("order_to_scatter_signal",false),1.0,1);
		}
		
		received_order_to_scatter_signals <- [];
	}
	
	/* message reception of injuries */
	action receive_injuries(agent violent_offender, float damage){
		invoke receive_injuries(violent_offender,damage);
		do add_belief(new_predicate("injuresMe",["damage"::damage],true,violent_offender),1.0,1); 
	}
	
	/* run the full list of emotional triggers */
	action process_events {
   		if is_event_to_detect["spatial_incursion"]{do check_spatial_incursion;}
   		if is_event_to_detect["outnumbered"]{do check_outnumbered;}
   		if is_event_to_detect["feeling_target_for_arrest"]{do check_feeling_target_for_arrest;}
   		if is_event_to_detect["being_arrested"]{do check_being_arrested;}
   		if is_event_to_detect["unjust_arrest_around"]{do check_unjust_arrest_around;}
   		if is_event_to_detect["surrounded"]{do check_surrounded;}
   		if is_event_to_detect["any_police_officer_around"]{do check_seen_police_officers;}
   		if is_event_to_detect["order_to_scatter_signal"]{do check_order_to_scatter_signal;}
   		do check_arrest_around;
   		if focus = self {
   			write "+++";
   			write is_event_detected;
   			write "+++";
   		}
   	}
   	   	
   	/// /// Emotional Contagion /// ///   	
   	
   	/* run the full process of emotional contagion manually for rioters */
   	action process_emotional_contagion{
   		if focus = self {write " -- process_emotional_contagion -- ";}
   		
   		loop single_rioter over:rioter at_distance view_dist{
   			float emotion_contagion_factor <- single_rioter.charisma*receptivity;
   			
   			if emotion_contagion_factor > emotional_contagion_threshold {
   				list<emotion> collected_emotions;
		   		ask single_rioter{
		   			if focus = self {
		   				write "seen rioter self.emotion_base:"+self.emotion_base;
		   			}
		   			loop single_emotion over:self.emotion_base{
		   				if single_emotion.name = "fear" 
		   				   or single_emotion.name = "fear_confirmed"  // potentially to remove
		   				   or single_emotion.name = "anger" // potentially to remove
		   				   or single_emotion.name = "sadness"
		   				   or single_emotion.name = "reproach"{
		   				   	add copy(single_emotion) to: collected_emotions;
		   				}
		   				
		   				/*
		   				else if single_emotion.name = "fear_confirmed" {
		   					emotion detected_emotion <- new_emotion("fear",
								get_intensity(single_emotion),
								get_about(single_emotion),
								get_decay(single_emotion),
								get_agent_cause(single_emotion)
							);
							add copy(detected_emotion) to: collected_emotions;
		   				}
		   				* 
		   				*/
		   			}
		   		}
		   			
		   		if focus = self {write "collected_emotions:"+collected_emotions;}
		   			
		   		
		   		loop single_collected_emotion over: collected_emotions{
		   			if focus = self {
		   				write "	++ predicates collected";
		   				write " ++" + single_collected_emotion.about;
		   			}
		   			
		   			emotion already_possessed_emotion <- get_emotion(single_collected_emotion);
		   			emotion result_emotion <- single_collected_emotion;
		   			float result_intensity;
		   			float result_decay;
		   			
		   			if focus = self {
			   			write "already_possessed_emotion:"+already_possessed_emotion;
			   			if !(already_possessed_emotion = nil) {
			   				write "	++ predicates already";
			   				write " ++" +already_possessed_emotion.about;
			   			}	
			   		}
		   			
		   			if already_possessed_emotion=nil {
		   				result_intensity <- single_collected_emotion.intensity*emotion_contagion_factor;
		   				result_decay <- single_collected_emotion.decay;
		   			} else {
		   				result_intensity <- 
			   				already_possessed_emotion.intensity
			   				+single_collected_emotion.intensity*emotion_contagion_factor;
			   				
			   				
			   			if already_possessed_emotion.intensity<single_collected_emotion.intensity{
			   				result_decay <- single_collected_emotion.decay;
			   			} else {
			   				result_decay <- single_collected_emotion.decay;
			   			}
			   			
		   			}
					result_emotion <- new_emotion(result_emotion.name,result_intensity,result_emotion.about,result_decay);		
					   			
		   			if focus = self {
			   			write result_emotion;
			   			write "new_emotion="+":"+string(result_emotion.intensity);
		   			}
					do add_emotion(result_emotion);
				}
   			}
	   	}
   	}
   	
   	/// /// Emotions /// ///
   	
   	/* inference process of the agent connecting beliefs to the predicates used in desires */
   	action handle_bdi_process_for_emotion(string emotion_name, predicate original_belief){
   		assert emotion_name in authorized_emotions;
   		
   		string belief_name <- original_belief.name;
   		agent belief_agent_cause <- original_belief.cause;
		
   		if emotion_name = "fear" {
   			do add_uncertainty(new_predicate("safe",["belief_name"::belief_name],false,belief_agent_cause),0.5,1);
   		} else if emotion_name = "anger" {
   			do add_belief(new_predicate("injustice",["belief_name"::belief_name],belief_agent_cause),1.0,1); 
   			do add_belief(new_predicate("injustice",["belief_name"::belief_name],belief_agent_cause),1.0,1);
   		} else if emotion_name = "fear_confirmed" {
   			do add_uncertainty(new_predicate("safe",["belief_name"::belief_name],false,belief_agent_cause),0.5,1);
   			do add_belief(new_predicate("safe",["belief_name"::belief_name],false,belief_agent_cause),1.0,1); 
   		}
   	}
   	
   	/*
   	 * Takes the events and correlates them to emotions depending on the current state of the agent
   	 */ 	
   	action create_emotions_from_direct_events {
   		loop state_name over: is_in_state.keys{
   			if is_in_state[state_name] and state_to_events_to_emotions.keys contains state_name{
	   			loop event_name over: is_event_to_detect.keys{
	   				if is_event_detected[event_name]{
	   					loop emotion_name over: state_to_events_to_emotions[state_name][event_name]{
	   						list<predicate> beliefs_from_event <- get_beliefs(
	   							new_predicate(event_name)
	   							) accumulate each; //each.predicate????????
	   						loop single_belief_from_event over: beliefs_from_event{
	   							do handle_bdi_process_for_emotion(emotion_name:emotion_name,original_belief:single_belief_from_event);
	   						}
	   					}
	   				}
	   			}
	   		}
   		}
   		if focus = self {
   			write name +" emotion_base:"+emotion_base;
   			write "+ has_fear:"+has_emotion(new_emotion("fear"));
   			write "+ has_fear_confirmed:"+has_emotion(new_emotion("fear_confirmed"));
   			write "+ has_anger:"+has_emotion(new_emotion("anger"));
   		}
   	}    
   	
   	/* set the intensity decay of all emotions */
   	action set_emotion_decay {
   		loop single_emotion over: emotion_base{
   			single_emotion <- new_emotion(single_emotion.name, single_emotion.intensity, single_emotion.about, P_emotion_decay);//set_decay(single_emotion,P_emotion_decay);
   		} 
   	}
    
    /* update the police liking (which translates into perceived hostility when it is negative) */
    action update_police_liking{
    	if focus = self {write " --- PSL "+name+" START --- ";}
    	
		list<emotion> police_induced_emotions <- (emotion_base select (species(each.cause) = police_officer and !dead(each.cause)));
		
		list<string> influencing_police_names; // only once each police officer causing emotions
		loop single_emotion over: police_induced_emotions{
			if !(single_emotion.cause.name in influencing_police_names){
				add single_emotion.cause.name to: influencing_police_names;
			}
		}		
		map<string,map<string,float>> emotion_to_police_name_to_max_induced;
		loop emotion_name over:(possible_positive_emotions+possible_negative_emotions){
			emotion_to_police_name_to_max_induced[emotion_name] <- [];
			loop police_cause_name over:influencing_police_names{
				emotion_to_police_name_to_max_induced[emotion_name][police_cause_name] <- 0.0;
			}
		}
		loop emotion_name over:(possible_positive_emotions+possible_negative_emotions){
			loop single_emotion over: police_induced_emotions{
				string police_cause_name <- single_emotion.cause.name;
				float se_intensity <- single_emotion.intensity;
				
				if single_emotion.name = emotion_name{
					if police_cause_name in emotion_to_police_name_to_max_induced[emotion_name].keys{
						if emotion_to_police_name_to_max_induced[emotion_name][police_cause_name] < se_intensity{
							emotion_to_police_name_to_max_induced[emotion_name][police_cause_name] <- se_intensity;
						}
					} else {
						emotion_to_police_name_to_max_induced[emotion_name][police_cause_name] <- se_intensity;
					}
				}
			} 
		}
		
		map<string,float> police_name_to_positive_influence;
		map<string,float> police_name_to_negative_influence;
		loop police_name over: influencing_police_names{
			police_name_to_positive_influence[police_name] <- 0.0;
			police_name_to_negative_influence[police_name] <- 0.0;
			
			loop positive_emotion_name over:possible_positive_emotions{
				if police_name in emotion_to_police_name_to_max_induced[positive_emotion_name].keys{					
					police_name_to_positive_influence[police_name] <- police_name_to_positive_influence[police_name] + 
						emotion_to_police_name_to_max_induced[positive_emotion_name][police_name]/N_possible_positive_emotions;
				}
			}
			
			loop negative_emotion_name over:possible_negative_emotions{
				if police_name in emotion_to_police_name_to_max_induced[negative_emotion_name].keys{
					police_name_to_negative_influence[police_name] <- police_name_to_negative_influence[police_name] + 
						emotion_to_police_name_to_max_induced[negative_emotion_name][police_name]/N_possible_negative_emotions;
				}
			}
		}
		
		loop police_name over: influencing_police_names{
			if !(police_name in police_social_liking_with.keys){
				police_social_liking_with[police_name] <- 0.0;	
			}
			if focus = self {
				write " -- prev_PSL:"+police_social_liking_with[police_name];
				write " -- added_PSL:"+(k_liking*(1-neurotism)
					*(police_name_to_positive_influence[police_name]-police_name_to_negative_influence[police_name])
					*(1-abs(police_social_liking_with[police_name]))*step);
				write " -- diff_emotions:"+(police_name_to_positive_influence[police_name]-police_name_to_negative_influence[police_name]);
				write " -- k_liking*(1-neurotism):"+(k_liking*(1-neurotism));
			}
			
			police_social_liking_with[police_name] <- 
			police_social_liking_with[police_name] + k_liking*(1-neurotism)
			*(police_name_to_positive_influence[police_name]-police_name_to_negative_influence[police_name])
			*(1-abs(police_social_liking_with[police_name]))*step;
			
			if focus = self {
				write "-- new PSL:"+police_social_liking_with[police_name];
			}
			
			if police_social_liking_with[police_name] < -1 { police_social_liking_with[police_name] <- -1.0;}
			if police_social_liking_with[police_name] > 1 { police_social_liking_with[police_name] <- 1.0;}
		}
		
		if focus = self {
			write "-- police_social_liking_with:"+police_social_liking_with;
		}
		
		if length(police_social_liking_with) > 0{
			aggregated_police_social_liking <- mean(police_social_liking_with.values);
		}
		
		if focus = self {
			write "-- aggregated_police_social_liking:"+aggregated_police_social_liking;
		}
		if focus = self {write " --- PSL "+name+" END --- ";}
		
	}
	
	/* update the overall psychological distress of the agent */
	action update_felt_negative_emotions{
		map<string,float> emotion_to_max_intensity;
		loop emotion_name over: possible_negative_emotions{
			emotion_to_max_intensity[emotion_name] <- 0.0;
		}
		
		loop single_emotion over:emotion_base{
			string se_name <- single_emotion.name ;
			float se_intensity <- single_emotion.intensity;
			
			if se_name in possible_negative_emotions{
				if se_intensity > emotion_to_max_intensity[se_name]{
					emotion_to_max_intensity[se_name] <- se_intensity;
				}
			}
		}
		
		felt_negative_emotions <- 0.0;
		loop emotion_name over:possible_negative_emotions{
			felt_negative_emotions <- felt_negative_emotions + 
				emotion_to_max_intensity[emotion_name]/N_possible_negative_emotions;
		}
	}
		
	/// /// Desires or state transitions /// ///
	predicate flock <- new_predicate("flock");
	predicate violent <- new_predicate("violent"); 
	predicate retreat <- new_predicate("retreat");
	
	map<string,bool> is_in_state <- [
		"flock"::false,
		"violent"::false,
		"retreat"::false
	];
	bool has_desire_flock update:has_desire_op(self,flock);
	bool has_desire_violent update:has_desire_op(self,violent);
	bool has_desire_retreat update:has_desire_op(self,retreat);
	
	/* adapt the current perceived state from the activated desire */
	action update_state_from_desires{
		assert has_desire_flock label:"should always have flock desire";
		assert int(has_desire_violent)+int(has_desire_retreat) < 2  label:"cannot have both violent and retreat desires:"+desire_base;
		
		
		is_in_state["flock"] <- has_desire_flock and !(has_desire_violent or has_desire_retreat);
		is_in_state["violent"] <- has_desire_violent;
		is_in_state["retreat"] <- has_desire_retreat;
		
		if (focus=self){
			//write "desire_base:"+desire_base;
			//write "is_in_state:"+is_in_state;
		}
	}
	
	/* update parameters related to violence transitions */
	action update_violence_parameters{
		list<rioter> potential_violent<-rioters_around select (has_desire_op(each,violent));
		N_violent_around<-1 + length(potential_violent);
		arrest_proba<-1-exp(-2.3*(N_police_officers_around/N_violent_around));
	}
	
	/* compute the police social liking influence on violence transitions */
	float compute_police_social_liking_influence{
		if focus = self{
			write "aggregated_police_social_liking="+aggregated_police_social_liking;
		}
		float police_social_liking_influence <- 1-max_liking_influence_to_violence*abs(aggregated_police_social_liking)*int(aggregated_police_social_liking<0);
		
		if focus = self{
			write "police_social_liking_influence="+police_social_liking_influence;
		}
		
		return police_social_liking_influence;
	}
	
	/* check the psychological distress is alarming */
	bool compute_feel_strong_negative_emotions{
		return felt_negative_emotions > retreat_threshold;
	}
	
	/* run the complete state transition process */
	action handle_state_transition {
		// neutral by default if no violent or retreat intention
		if (focus=self){
			write "INFO: state_transition "+self.name +" curr intention:"+get_current_intention_op(self);
			//write "belief_base:"+belief_base;
			//write "has_belief(new_predicate('triedRetreat')):"+has_belief(new_predicate("triedRetreat"));
		}
		
		if is_in_state["violent"]{
			if compute_feel_strong_negative_emotions() and !(has_belief(new_predicate("triedRetreat"))) {  
				// 5
				do remove_intention(violent,true);
				do add_desire(retreat,20.0,5);
			} else {
				bool seen_any_arrest_around <-((get_belief(new_predicate("arrest_around")).predicate) );
				if focus = self {
					write " çççç ";
					write "seen_any_arrest_around:"+seen_any_arrest_around;
					write "is_event_detected['arrest_around']:"+is_event_detected['arrest_around'];
					write "(grievance-risk_aversion*arrest_proba) < attack_threshold*threshold_ratio_violence_to_neutral*compute_police_social_liking_influence():";
					write "grievance:"+grievance;
					write "risk_aversion*arrest_proba:"+risk_aversion*arrest_proba;
					write "attack_threshold:"+attack_threshold;
					write "threshold_ratio_violence_to_neutral:"+threshold_ratio_violence_to_neutral;
					write "compute_police_social_liking_influence():"+compute_police_social_liking_influence();
					write ""+(grievance-risk_aversion*arrest_proba) + "<" + attack_threshold*threshold_ratio_violence_to_neutral*compute_police_social_liking_influence();
					write " çççç ";
				}
				if (seen_any_arrest_around and (grievance-risk_aversion*arrest_proba) < attack_threshold*threshold_ratio_violence_to_neutral*compute_police_social_liking_influence()) {
					// 2
					do remove_intention(violent,true);
				}
			}
			
		} else if is_in_state["retreat"]{
			//has_belief(new_predicate("surrounded")){
			if ((grievance-risk_aversion*arrest_proba*int(has_belief(new_predicate("surrounded")))) > attack_threshold*compute_police_social_liking_influence())
				and (current_energy > energy_minimum){
				// 6
				do remove_intention(retreat,true);
				do add_desire(violent,10.0,5);
			} else if !compute_feel_strong_negative_emotions() {
				// 4
				do remove_intention(retreat,true);
			}
			
		} else {
			//write "grievance-risk_aversion*arrest_proba) > attack_threshold*compute_police_social_liking_influence():";
			//write ""+grievance+"-"+risk_aversion+"*"+arrest_proba+" > "+attack_threshold+"*"+compute_police_social_liking_influence();
			//write ""+(grievance-risk_aversion*arrest_proba)+" > "+attack_threshold*compute_police_social_liking_influence();
			//write "current_energy > energy_minimum):"+current_energy+">"+energy_minimum;
			if ((grievance-risk_aversion*arrest_proba) > attack_threshold*compute_police_social_liking_influence()) and (current_energy > energy_minimum) {
				// 1
				do add_desire(violent,10.0,5);
			} else if compute_feel_strong_negative_emotions(){  // and !(has_belief(new_predicate("triedRetreat"))) 
				// 3
				do add_desire(retreat,20.0,5);
			}
		}
		
		if (focus=self){
			//write "new desire_base:"+desire_base;
		}
	}
	
	/* run the complete decision process of the agent */
	reflex complete_decision_process{
		// do flush_emotion_base;
		do update_state_from_desires;
 
   		if emotional_contagion_activated {
			do process_emotional_contagion;
		} 
		
		do process_events;
		do create_emotions_from_direct_events;
		
		do set_emotion_decay;
		
		do update_police_liking;
		do update_felt_negative_emotions;
		do update_violence_parameters;
		
		do handle_state_transition;
	}
		
	/// /// /// /// PLANS /// /// /// ///
	
	/* compute the boid repulsion coming from the closest officer */
	action influence_police_officer {
		police_officer closest_officer <- (police_officer at_distance (sent_dist_repulsion*2)) closest_to self;
		if closest_officer != nil {
			do influence_repulsion(closest_officer.location,1.0);
		}
	}
	
	/* compute the flock movement with a malus to slightly escape from police officers */
	action flock{
		do influence_police_officer;
		invoke flock();
	}
	
	/* simply flock with the boid 3 rules */
	plan flocking intention:flock{
		if (focus=self){
			write "-- PLAN flocking -- of "+name;
			//write "INFO:"+self.name +" curr intention:"+get_current_intention_op(self); 
		}
		
		do add_belief(flock,1.0,1); // one cycle lifetime
		do add_desire(flock);
		do flock();
	}
	
	/* flee from the police officers */
	plan retreat intention:retreat{
		if (focus=self){
			write "-- PLAN retreat -- of "+name;
		}
		
		do add_belief(new_predicate("triedRetreat"),1.0,lifetime_triedRetreat);
		
		list<police_officer> officers_around <- police_officer at_distance view_dist;
		
		if !(empty(officers_around)){
			point avg_flee_vector;
			
			ask computer {
				list<point> officers_flee_vectors;
				loop single_officer over: officers_around{
					//write "get vector to officer";
					add get_vector_in_torus_perception(single_officer.location,myself.location,myself.view_dist) to: officers_flee_vectors;
				}
				avg_flee_vector <- compute_weighted_avg_points(officers_flee_vectors, officers_flee_vectors accumulate 1.0);
				}
						
			heading <- atan2(avg_flee_vector.y,avg_flee_vector.x);
		}
		do move_in_free_space; // same direction otherwise
	}
	
	/* turn violent and attack a victim (officer or item) */
	plan attack_victim_target intention:violent{
		if (focus=self){
			write "-- PLAN attack_victim_target -- of "+name;
		}
		
		//write "INFO:"+get_current_intention_op(self);
		
		//if the agent does not have chosen a target location, it adds the sub-intention to define a target and puts its current intention on hold
		//write "before victim_target=nil condition";
		//write "victim_target  ="+victim_target;
		if (victim_target = nil or dead(victim_target)) {
			//write "add subintention";
			do add_subintention(get_current_intention(),defineVictimTarget, true);
			do current_intention_on_hold();
			//write "end add subintention";
		} else {
			//write "move to victim_target";
			point move_vector;
			ask computer{
				//write "get vector torus repulsion";
				move_vector<-get_vector_in_torus_perception(myself.location,myself.victim_target.location,myself.view_dist);
			}
			heading<-atan2(move_vector.y,move_vector.x);
			do move_in_free_space;
			
			if ((victim_target.location distance_to location)<attack_dist and (current_energy > energy_minimum))  {
				//write " - attack victim_target";
				mental_state curr_desire_violent <- get_desire_op(self,violent);
				//write " - curr_desire_violent";
				do add_belief(violent,1.0,1);
				//write " - added belief_violent";
				do add_desire(violent, 10.0, curr_desire_violent.lifetime);
				//write " - added desire_violent";
				current_energy <- current_energy - energy_attack_consumption;
				ask victim_target{
					//write "hurt";
					do receive_injuries(myself,1.0);
					//write "receive injuries";
				}
				record_damage_done <- record_damage_done + 1.0;
				//write " - done attack victim_target";
			}
			//write "done move to victim_target";
		}	
	}
	
	/* compute the utility of attacking a given agent */
	float compute_utility_attacking(breakable_item potential_victim){
		float utility_attacking <- 1.0;
		
		//utility_attacking <- utility_attacking*potential_victim.resistance_init;
		
		float dist <- self distance_to potential_victim;
		utility_attacking <- dist>0? utility_attacking/(dist^2):1e9;
		
		int count_same_victim <- 1;
		ask rioter {
			if (self.victim_target = potential_victim){
				count_same_victim <- count_same_victim + 1;
			}
		}
		utility_attacking <- utility_attacking*ln(2+count_same_victim)/ln(2);
		
		return utility_attacking;
	}
	
	/* select the victim */
	plan choose_victim_target intention:defineVictimTarget instantaneous:true{
		if (focus=self){
			write "-- PLAN choose_victim_target -- of "+name;
		}
		//write "choose victim_target";
		list<breakable_item> potential_victims;
		loop single_belief over:get_beliefs(new_predicate("locationPotentialVictim")){
			predicate single_predicate<-mental_state (single_belief).predicate;
			
			if !dead(single_predicate.cause){
				add breakable_item(single_predicate.cause) to:potential_victims;
			}
		}
		
		if (empty(potential_victims)) {
			do flock();
		} else {
			float max_utility<--1.0;
			float evaluated_utility;
			loop evaluated_victim over: potential_victims{
				evaluated_utility<-compute_utility_attacking(evaluated_victim);
				if (evaluated_utility > max_utility){
					victim_target <- evaluated_victim;
					max_utility <- evaluated_utility;					
				}
			}
		}
		do remove_intention(defineVictimTarget, true);
		//write "done victim_target";
	}
		
	
	
	init {
		loop single_state over: state_to_events_to_emotions.keys {
			assert authorized_states contains single_state;
		}
		
		loop event_to_emotions over: state_to_events_to_emotions {
			loop single_event over: event_to_emotions.keys{
				//assert is_event_to_detect.keys contains single_event;
				//is_event_to_detect[single_event] <- true;
				
				loop single_emotion over: event_to_emotions[single_event]{
					assert authorized_emotions contains single_emotion;
				}
			}
		} 
		
		do add_desire(flock);
		
		do add_desire(new_predicate("injustice",false));
		do add_desire(new_predicate("safe",true));
		do add_ideal(new_predicate("injustice"),-1.0);
	}
	
	reflex update_my_color_to_emotion_negative{
		my_color <- rgb(int(felt_negative_emotions*255),0,int((1-felt_negative_emotions)*255));
	}
	aspect emotion_negative {
		draw arrow_shape() color: my_color;
	}
	aspect state{
		if has_desire_violent{
			draw arrow_shape() color: #red;
		} else if has_desire_retreat{
			draw arrow_shape() color: #green;
		} else {
			draw arrow_shape() color: #black;
		}
	}
}

