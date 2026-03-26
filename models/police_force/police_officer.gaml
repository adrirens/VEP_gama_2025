/**
* Name: policeofficer
* Based on the internal empty template. 
* Author: julien-rsbrg
* Tags: 
*/


model policeofficer

import "../utils.gaml"
import "../citizen/rioter.gaml"
import "../police_force/team.gaml"
import "../police_force/arrest_team.gaml"
import "../unanimate/items.gaml"
import "../moussaid_model.gaml"

/* species of police officers for peace maintenance in the protest */
species police_officer parent:basic_pedestrian control:simple_bdi skills:[moving]{
	float m <- rnd(P_m_min,P_m_max);
	float size <- m/320.0;
	float shape_angle <- 150.0;
	rgb my_color<-#blue;
	bool can_die <- false;
	
	float view_dist <- P_dmax; // TO GIVE
	float view_dist_alert <- P_dmax;
	float arrest_dist <- P_arrest_dist;
	float dmax_my_position_team <- P_dmax_my_position_team;
	
	
	geometry arrow_shape(float size, float shape_angle){
		point X_head<-{size*cos(heading),size*sin(heading)}+location;
		point X_back_left<-{size*cos(heading+shape_angle),size*sin(heading+shape_angle)}+location;
		point X_back_right<-{size*cos(heading-shape_angle),size*sin(heading-shape_angle)}+location;
		return polygon([X_head,X_back_left,X_back_right]);
	}
	
	aspect base {
		draw arrow_shape(size,shape_angle) color: my_color;
	}
	
	aspect vision {
		draw circle(view_dist) color: #red;
	}
	
	user_command focus {
		focus <- self;
	}
	
	/////////////////////////// BDI Architecture /////////////////////////////////////////
	
	// PARAMETERS
	bool use_emotions_architecture <- true;
    bool use_personality <- true;
    float extroversion <- rnd(1.0);
	float neurotism <- rnd(rnd(0.2,0.4),1.0);
	float charisma <- extroversion;
	float receptivity <- 1-neurotism;
	float inter_species_receptivity <- rnd(receptivity);
    float conscientiousness <- 1.0;
    float emotional_contagion_threshold <- P_emotional_contagion_threshold;
    
    float resistance_init<-P_police_resistance_init;
	
	float threshold_alert <- rnd(0.4,1.0);
	// Team parameters
	team my_team;
	point my_position_team <- location;
	float violence_threshold <- rnd(1.0); 
	
	arrest_team my_arrest_team;
	point my_position_arrest_team <- location;
	agent my_arrest_target;
	float record_arrest_contribution;
	
	float felt_negative_emotions;
	/* receive and store the target position assigned by the team */
	action receive_my_position_from_team (point sent_position) {
		//write "receive_my_position_from_team";
		my_position_team <- sent_position;
	}
	
	/* receive and store the position assigned by the arrest team */
	action receive_my_position_from_arrest_team (point sent_position) {
		my_position_arrest_team <- sent_position;
	}
	
	/* receive the agent to arrest */
	action receive_my_arrest_target (agent sent_arrest_target) {
		my_arrest_target <- sent_arrest_target;
	}
	
	
	// DESIRES
	/*It is the state not emotionnal but the state order by his team */
	predicate keepFormation <- new_predicate("keepFormation");
	predicate protect <- new_predicate("protect"); 
	predicate back <- new_predicate("back");
	// injuresMe (only by keyword)
	// loseFight (only by keyword)
	
	// (specifically) BELIEFS
	// keepFormation, protect
	// injuresMe, uncertainty(loseFight), loseFight, locationPotentialArrest, arrestTarget
	// nameAgentFormationWith
	
	list<rioter> detected_violent_offenders update: detected_violent_offenders at_distance view_dist;//handled by hand
	list<rioter> rioter_around update: rioter at_distance view_dist;//handled by hand
	list<police_officer> police_officer_around update: police_officer at_distance view_dist;//handled by hand
	
	
	/* receive the information that a violent offender is around (e.g., because in vision range).
	 * 
	 * This message can be sent from the violent offender itself while committing the act.
	 */
	action receive_violent_offender(rioter violent_offender){   		
   		if !(self.detected_violent_offenders contains violent_offender){
   			detected_violent_offenders <- detected_violent_offenders + [violent_offender];
   		}
   	}
   	
	
	// (specifically) INTENTIONS
	// keepFormation, protect (intendToProtect, defineVictimTarget), retreat
	predicate opportunityToArrest <- new_predicate("opportunityToArrest");
	
	
	
	// RULES
	rule desire:retreat remove_intention:protect;
	
	// PERCEPTION/RULES
	map<string,bool> is_in_state <- [
		"formation"::false,
		"protect"::false,
		"back"::false
	];
	bool has_desire_formation update:has_desire_op(self,keepFormation);
	bool has_desire_protect update:has_desire_op(self,protect);
	bool has_desire_back update:has_desire_op(self,back);
	
	/* update internal state variables based on current desires */
	action update_order_from_desires{
		assert has_desire_formation label:"should always have formation desire";
		assert int(has_desire_protect)+int(has_desire_back) < 2  label:"cannot have both protect and retreat desires:"+desire_base;
		if (focus=self){write "desire_base:"+desire_base;}
		
		is_in_state["formation"] <- has_desire_formation and !(has_desire_protect or has_desire_back);
		is_in_state["protect"] <- has_desire_protect;
		is_in_state["retreat"] <- has_desire_back;
	}
	
	/* handles the reception of injuries */
	action receive_injuries(agent violent_offender, float damage) {
		//write "-- "+name+" enter receive_injuries";
		invoke receive_injuries(violent_offender,damage);
		//write "-- "+name+" done invoke";
		do add_belief(new_predicate("injuresMe",["damage"::damage],true,violent_offender),1.0,-1); 
		//write "-- "+name+" done new_belief";
	}
	
	/* check that an arrest is possible */
	reflex update_opportunityToArrest {			
		if (length(detected_violent_offenders)>0){
			do add_belief(opportunityToArrest,1.0,1);
			ask my_team{
				do receive_detected_violent_offenders(myself.detected_violent_offenders);
			}
		}
	}
	
	/* receive order to join an arrest team  */
	action receive_arrest_order(arrest_team new_arrest_team, point new_position_arrest_team, agent new_arrest_target){
		if focus=self {write name + "received arrest_order";}
		my_arrest_team <- new_arrest_team;
		my_position_arrest_team <- new_position_arrest_team;
		my_arrest_target <- new_arrest_target;
		do add_desire(protect,10.0,-1);
	}
	
	/* end the officer's contribution to an arrest */
	action end_arrest_contribution{
		do send_end_arrest_contribution;
		
		my_arrest_team <- nil;
		my_position_arrest_team <- nil;
		my_arrest_target <- nil;
		do remove_intention(protect,true);
		
		ask my_team{
			do return_member_from_arrest_team(myself);			
		}
	}
	
	/* receive end of arrest order */
	action receive_end_of_arrest{
		if focus=self {write name + "received end_of_arrest";}
		do end_arrest_contribution;
	}
	
	/* send a notification to the arrestteam that this officer is done contributing */
	action send_end_arrest_contribution{
		assert my_arrest_team != nil;
		ask my_arrest_team {
			do receive_end_arrest_contribution(old_member:myself);
		}
	}
	
	// PLANS
	
	/* move officer to their assigned formation position */
	plan keep_formation intention:keepFormation {
		if (focus=self){
			write "-- PLAN keep_formation -- of "+name;
			write "  moving to my_position_team:"+my_position_team;
		}
		
		do add_belief(keepFormation,1.0,1); // one cycle lifetime
		do add_desire(keepFormation);
		
		do move_to(my_position_team);
	}
	
	/* flee from the isobarycenter of detected violent offenders */
	plan retreat intention:back{
		if (focus=self){write "-- PLAN retreat -- of "+name;}
		
		if (empty(detected_violent_offenders)){
			do move; // keep the same movement
		} else {
			point retreat_vector;
			
			ask computer {
				list<point> offenders_flee_vectors;
				loop single_offender over: myself.detected_violent_offenders{
					add get_vector_in_torus_perception(single_offender.location,myself.location,myself.view_dist) to: offenders_flee_vectors;
				}
				retreat_vector <- compute_weighted_avg_points(offenders_flee_vectors, offenders_flee_vectors accumulate 1.0);
			}
			
			point retreat_centroid <- location - retreat_vector ;
			do move_away_from(retreat_centroid);
		}
	}
	
	

	/* run the arrest process against violent offender. The agent should be in an arrest_team. */
	plan arrest intention:protect{
		if (focus=self){write "-- PLAN arrest_target -- of "+name;}
		
		assert my_arrest_team!=nil;
		assert my_arrest_target!=nil;
		
		if focus = self {
			write '(location distance_to my_position_team) > dmax_my_position_team';
			write string(location distance_to my_position_team) + ">" +dmax_my_position_team;
			write (location distance_to my_position_team) > dmax_my_position_team;
		}
		
		if (location distance_to my_position_team) > dmax_my_position_team {
			if focus = self {write 'end_arrest_contribution';}
			do end_arrest_contribution;
		} else {
			if focus = self {write 'move_to('+my_position_arrest_team+')';}
			do move_to(my_position_arrest_team);
			
			if ((my_arrest_target distance_to location) < arrest_dist){
				do add_belief(protect,1.0,1);
				do add_desire(protect,10.0,-1);
				
				ask my_arrest_team {
					do receive_arrest_contribution(1);
				}
				record_arrest_contribution <- record_arrest_contribution + 1;
			}
		}
		
		
		
	}
	
	/// /// list of emotional triggers /// ///
   	float dist_spatial_incursion <- P_rioter_dist_spatial_incursion;
   	
   	float ratio_cop_over_policer_outnumbered <- P_rioter_ratio_cop_over_rioter_outnumbered * 3;
   	
   	/* check spatial incursion with police officers */
   	action check_spatial_incursion {
   		rioter closest_rioter <- rioter_around closest_to self;
   		if closest_rioter != nil {
   			is_event_detected["spatial_incursion"] <-  (
	   			closest_rioter distance_to self < dist_spatial_incursion
	   		);
   		} else {
   			is_event_detected["spatial_incursion"] <- false;
   		}
   		
   		
   		if is_event_detected["spatial_incursion"] {
			loop single_officer over: (rioter_around at_distance dist_spatial_incursion){
				do add_belief(new_predicate("spatial_incursion",single_officer),1.0,1);
			}
		} else {
			do add_belief(new_predicate("spatial_incursion",false),1.0,1);
		}
   	}
   	
   	/* check rioters are currently outnumbered by police officers around the agent */
   	action check_outnumbered {
   		int N_police_officer_around <- length(police_officer_around)+1;
   		is_event_detected["outnumbered"] <- (
   			(length(rioter_around)+1)/N_police_officer_around > ratio_cop_over_policer_outnumbered
   		);
   		
   		if is_event_detected["outnumbered"]{
			loop single_rioter over: rioter_around{
				do add_belief(new_predicate(
					"outnumbered",
					single_rioter			
				),1.0,1);
			}
		} else {
			do add_belief(new_predicate("outnumbered",false),1.0,1);
		}
   	}
   	
   	
   
   	/* check being surrounded by walls or police officers */
   	action check_surrounded{
		ask computer  {
			myself.is_event_detected["surrounded"] <- is_surrounded(
				obstacles:list(rioter),
				n_subdivisions_to_surround:3, 
				n_subdivisions:4, 
				origin_location:myself.location,
				perception_distance:myself.view_dist, 
				init_angle:rnd(360.0)
			);
		}
		if is_event_detected["surrounded"] {
			loop single_rioter over: rioter_around{
				do add_belief(new_predicate("surrounded",single_rioter),1.0,1);
			}
		} else {
			do add_belief(new_predicate("surrounded",false),1.0,1);
		}
	}
	
	action process_events {
   		if is_event_to_detect["spatial_incursion"]{do check_spatial_incursion;}
   		if is_event_to_detect["outnumbered"]{do check_outnumbered;}
   		if focus = self {
   			write "+++";
   			write is_event_detected;
   			write "+++";
   		}
   	}
   	
	
	
	/* run the full process of emotional contagion manually for police officers */
   	action process_emotional_contagion{
   		if focus = self {write " -- process_emotional_contagion -- ";}
   		do emotion_contagion_for_policeman;
   		
   		if inter_emotional_contagion{
   			do emotion_contagion_for_rioter;
   		}
   		
   		
   	}
   	
   	action emotion_contagion_for_rioter{
   		loop single_rioter over:rioter at_distance view_dist{
   			float emotion_contagion_factor <- single_rioter.charisma*receptivity*inter_species_receptivity;
   			
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
					result_emotion <- new_emotion(contrary_emotion[result_emotion.name],result_intensity,result_emotion.about,result_decay);		
					   			
		   			if focus = self {
			   			write result_emotion;
			   			write "new_emotion="+":"+string(result_emotion.intensity);
		   			}
					do add_emotion(result_emotion);
				}
   			}
	   	}
   	}
   	
   	action emotion_contagion_for_policeman{
   		loop single_police_officer over:police_officer at_distance view_dist{
   			float emotion_contagion_factor <- single_police_officer.charisma*receptivity;
   			if emotion_contagion_factor > emotional_contagion_threshold {
   				list<emotion> collected_emotions;
		   		ask single_police_officer{
		   			if focus = self {
		   				write "seen single_police_officer self.emotion_base:"+self.emotion_base;
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
   	 map<string,map<string,list<string>>> state_to_events_to_emotions <- P_state_to_events_to_emotions;
   	 list<string> authorized_states <- ["violent","retreat","alert","calm"];
   	 map<string,bool> is_event_to_detect <- [
	    "spatial_incursion"::P_spatial_incursion_to_detect,
	    "outnumbered"::P_outnumbered_to_detect,
	    "order_to_scatter_signal"::P_order_to_scatter_signal_to_detect
    ];
    map<string,bool> is_event_detected <- copy(is_event_to_detect) update:convert_map_values_to_false(is_event_detected);
    
    map<unknown,bool> convert_map_values_to_false(map<unknown,bool> map_to_bool){
    	loop k over:map_to_bool.keys{
    		map_to_bool[k]<-false;
    	}
    	return map_to_bool;
    }
   	list<string> authorized_emotions <- ["fear","anger","fear_confirmed"];
   	
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
   	 * Takes the events and correlates them to emotions depending on the current state of the agent*/ 	
   	action create_emotions_from_direct_events {
   		loop state_name over: is_in_state_behavior.keys{
   			if is_in_state_behavior[state_name] and state_to_events_to_emotions.keys contains state_name{
	   			loop event_name over: is_event_to_detect.keys{
	   				if is_event_detected[event_name]{
	   					loop emotion_name over: state_to_events_to_emotions[state_name][event_name]{
	   						list<predicate> beliefs_from_event <- get_beliefs(
	   							new_predicate(event_name)
	   							) accumulate mental_state (each).predicate; 
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
   	
   	bool has_fear;
   	bool has_fear_confirmed; 
   	bool has_sadness;
   	bool has_anger;
   	bool has_joy;
   	float fear_rate <- 0.05;
   	/* set the intensity decay of all emotions */
   	action set_emotion_decay {
   		has_fear_confirmed <- false;
   		has_fear <- false;
   		has_sadness <- false;
   		has_anger <-false;
   		has_joy <- false;
   		loop single_emotion over: emotion_base{
   			single_emotion <- new_emotion(single_emotion.name, single_emotion.intensity, single_emotion.about, P_emotion_decay);//set_decay(single_emotion,P_emotion_decay);
   			if single_emotion.name = "fear" and single_emotion.intensity > fear_rate{
   				has_fear <- true;
   			}
   			if single_emotion.name = "fear_confirmed" and single_emotion.intensity > fear_rate{
   				has_fear_confirmed <- true;
   			}
   			if single_emotion.name = "anger" and single_emotion.intensity > fear_rate{
   				has_anger <- true;
   			}
   			if single_emotion.name = "joy" and single_emotion.intensity > fear_rate{
   				has_joy <- true;
   			}
   			if single_emotion.name = "sadness" and single_emotion.intensity > fear_rate{
   				has_sadness <- true;
   			}
   		} 
   	}
   	
	/// /// Desires or state transitions /// ///
	predicate calm <- new_predicate("calm");
	predicate alert <- new_predicate("alert");
	predicate violent <- new_predicate("violent"); 
	predicate retreat <- new_predicate("retreat");
	
	map<string,bool> is_in_state_behavior <- [
		"calm"::false,
		"alert"::false,
		"violent"::false,
		"retreat"::false
	];
	bool has_desire_calm update:has_desire_op(self,calm);
	bool has_desire_alert update:has_desire_op(self,alert);
	bool has_desire_violent update:has_desire_op(self,violent);
	bool has_desire_retreat update:has_desire_op(self,retreat);
	
	/* adapt the current perceived state from the activated desire */
	action update_state_bis_from_desires{
		assert has_desire_calm label:"should always have calm desire";
		assert int(has_desire_violent)+int(has_desire_retreat) < 2  label:"cannot have both violent and retreat desires:"+desire_base;
		
		
		is_in_state_behavior["calm"] <- has_desire_calm and !(has_desire_violent or has_desire_retreat or has_desire_alert);
		is_in_state_behavior["alert"] <- has_desire_alert;
		is_in_state_behavior["violent"] <- has_desire_violent;
		is_in_state_behavior["retreat"] <- has_desire_retreat;
		
		if (focus=self){
			//write "desire_base:"+desire_base;
			//write "is_in_state:"+is_in_state;
		}
	}
	
	float violence_detected{
		return length(detected_violent_offenders) / (length(rioter_around) + length(police_officer_around));
	}
	float alert_threshold <- rnd(violence_threshold);
	bool retreat_order <- false;
	bool imminent_danger <- false;
	
	/*the du=ifferents transitions between the sate that apolice man could be */
	action handle_state_transition {
		// neutral by default if no violent or retreat intention
		if is_in_state_behavior["alert"]{
			if violence_detected() > violence_threshold {
				do remove_intention(alert,true);
				do add_desire(violent,20.0,5);
			}
			else if  retreat_order or imminent_danger {
				do remove_intention(alert,true);
				do add_desire(retreat,20.0,5);
			}
		}
		else if is_in_state_behavior["violent"]{
			if violence_detected() < violence_threshold {
				do remove_intention(violent,true);
				do add_desire(alert,20.0,5);
			}
			else if  retreat_order or imminent_danger {
				do remove_intention(violent,true);
				do add_desire(retreat,20.0,5);
			}
		}else if is_in_state_behavior["retreat"]{
			if !(retreat_order or imminent_danger) {
				do remove_intention(retreat,true);
				do add_desire(alert,20.0,5);
			}
			if  !(retreat_order or imminent_danger) and violence_detected() > violence_threshold{
				do remove_intention(retreat,true);
				do add_desire(violent,20.0,5);
			}
		}else{
			if violence_detected() > alert_threshold or has_desire_protect{
				do add_desire(alert,20.0,5);
			}
		}
	}
	
	bool emotional_contagion_activated <- P_emotional_contagion_activated;
	reflex{
		do update_state_bis_from_desires;
		if emotional_contagion_activated {
			do process_emotional_contagion;
		} 
		
		do process_events;
		do create_emotions_from_direct_events;
		
		do set_emotion_decay;
		do handle_state_transition;
	}
	
	init {
		
		do add_desire(keepFormation);
		do add_desire(calm);
		//do add_desire(protect);
		
		do add_desire(new_predicate("injuresMe",false));
		do add_ideal(new_predicate("injuresMe"),-1.0,-1);
		
		//write "cop "+name+" is created - arrest_dist: "+arrest_dist;
	}
}
