/**
* Name: arrestteam
* Based on the internal empty template. 
* Author: julien-rsbrg
* Tags: 
*/


model arrestteam

import '../citizen/rioter.gaml'

/* abstract species handling the arrest of a violent offender by police officers */
species arrest_team {
	rioter arrest_target; // TO GIVE
	geometry to_target_cone;
	bool display_to_target_cone <- false;
	
	list<police_officer> members;
	police_officer member_closest_to_target;
	
	int faced_resistance_init;
	int current_faced_resistance;
	
	float view_dist <- P_dmax;
	float teta0 <- P_teta0;
	int n_min_members <- P_arrest_team_n_min_members;
	
	int creation_cycle;
	float time_before_starting_arrest <- P_time_before_starting_arrest;
	
	init {
		faced_resistance_init <- arrest_target.arrest_resistance_init;
		current_faced_resistance <- faced_resistance_init;
		creation_cycle <- cycle;
	}
	
	user_command focus {
		focus <- self;
	}
	
	/* Adds a police officer to the arrest team if not already a member */
	action receive_member(police_officer new_member){
		if !(new_member in members){
			add new_member to: members;
		}
	}
	
	/* Handles the removal of a member and closes the arrest if too few remain */
	action receive_end_arrest_contribution(police_officer old_member){
		members <- members-old_member;
		if length(members) < n_min_members {
			do close_arrest;
		}
	}
	
	/* Reduces the target's resistance based on the member's contribution */
	action receive_arrest_contribution(int contribution){
		current_faced_resistance <- current_faced_resistance - contribution;
	}
	
	/* Terminates the arrest */
	action close_arrest{
		loop single_member over: members {
			ask single_member {
				do receive_end_of_arrest;
			}
		}
		do die;
	}
	
	/* Checks if the arrest process should end */
	reflex check_end_process {
		if (current_faced_resistance <= 0){
			ask arrest_target{
				do die;
			}
		}
		
		if (arrest_target = nil or dead(arrest_target) or length(members)=0){
			do close_arrest;
		}
	}
	
	/* pdates the arrest team’s location */
	reflex update_location {
		// "-- update_location --";
		//write "members:"+members;
		//write "arrest_target:"+arrest_target;
		member_closest_to_target <- (members select !dead(each)) with_min_of (each distance_to arrest_target);
		location <- member_closest_to_target.location;
	}
	
	/*  Ends the arrest if the team loses visual contact with the target */
	reflex update_lose_target {
		if (member_closest_to_target distance_to arrest_target > view_dist){
			do close_arrest;
		}
	}
	
	/* Sends the arrest target’s location to team members after a delay */
	reflex send_order_locations{
		if focus=self {
			write ""+string((cycle - creation_cycle)*step)+">"+ string(time_before_starting_arrest) +"?";
		}
		if ((cycle - creation_cycle)*step > time_before_starting_arrest ){
			loop ms over: members {
				ask ms {
					do receive_my_position_from_arrest_team(myself.arrest_target.location);
				}
			}
		}
	}
	
	/* Updates the visual cone used to track the target */
	reflex update_to_target_cone {
		
		ask computer {
			//write 'get vector to target arrest team';
			point vector_to_target <- get_vector_in_torus_perception(origin:myself.location, destination:myself.arrest_target.location,max_dist:myself.view_dist);
			//write 'done get vector to target arrest team';
			float angle_to_target <- atan2(vector_to_target.y,vector_to_target.x);
			
			myself.to_target_cone <- create_part_circle(
				center_location:myself.location,
				complete_angle:myself.teta0,
				init_angle:angle_to_target-myself.teta0/2,
				n_vertices:4,
				radius:myself.view_dist
			);
		}
	}
	
	aspect base {
		draw circle(0.25#m) color:#darkred at:arrest_target.location;
		
		if display_to_target_cone{
			draw to_target_cone color:#darkred;
		}
	}
}
