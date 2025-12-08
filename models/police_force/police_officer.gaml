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
    
    float resistance_init<-P_police_resistance_init;
	
	
	// Team parameters
	team my_team;
	point my_position_team <- location;
	
	arrest_team my_arrest_team;
	point my_position_arrest_team <- location;
	agent my_arrest_target;
	float record_arrest_contribution;
	
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
	predicate keepFormation <- new_predicate("keepFormation");
	predicate protect <- new_predicate("protect"); 
	predicate retreat <- new_predicate("retreat");
	// injuresMe (only by keyword)
	// loseFight (only by keyword)
	
	// (specifically) BELIEFS
	// keepFormation, protect
	// injuresMe, uncertainty(loseFight), loseFight, locationPotentialArrest, arrestTarget
	// nameAgentFormationWith
	
	list<rioter> detected_violent_offenders update: detected_violent_offenders at_distance view_dist;//handled by hand
	
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
	
	init {
		do add_desire(keepFormation);
		//do add_desire(protect);
		
		do add_desire(new_predicate("injuresMe",false));
		do add_ideal(new_predicate("injuresMe"),-1.0,-1);
		
		//write "cop "+name+" is created - arrest_dist: "+arrest_dist;
	}
	
	// RULES
	rule desire:retreat remove_intention:protect;
	
	// PERCEPTION/RULES
	map<string,bool> is_in_state <- [
		"formation"::false,
		"protect"::false,
		"retreat"::false
	];
	bool has_desire_formation update:has_desire_op(self,keepFormation);
	bool has_desire_protect update:has_desire_op(self,protect);
	bool has_desire_retreat update:has_desire_op(self,retreat);
	
	/* update internal state variables based on current desires */
	action update_state_from_desires{
		assert has_desire_formation label:"should always have formation desire";
		assert int(has_desire_protect)+int(has_desire_retreat) < 2  label:"cannot have both protect and retreat desires:"+desire_base;
		if (focus=self){write "desire_base:"+desire_base;}
		
		is_in_state["formation"] <- has_desire_formation and !(has_desire_protect or has_desire_retreat);
		is_in_state["protect"] <- has_desire_protect;
		is_in_state["retreat"] <- has_desire_retreat;
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
	reflex update_opportunityToArrest{			
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
	plan retreat intention:retreat{
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
}
