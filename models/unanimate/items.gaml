/**
* Name: items
* Based on the internal empty template. 
* Author: julien-rsbrg
* Tags: 
*/


model items

import "../police_force/police_officer.gaml"

species obstacle schedules: []{}

species breakable_item parent: obstacle {
	
	float resistance_init;
	float current_resistance<-resistance_init;
	// could ask once for those values
	float police_view_dist <- P_dmax;
	float rioter_view_dist <- max(P_flocking_dist_attraction,P_flocking_dist_imitation,P_flocking_dist_repulsion); 
	
	bool can_die<-true;
	action receive_injuries(agent violent_offender, float damage){
		current_resistance<-current_resistance-damage;
		if (current_resistance<=0 and can_die){
			do die;
		}
		
		list<police_officer> perceived_officers<-length(police_officer)=0 ? [] : (police_officer at_distance police_view_dist);
		loop officer over:perceived_officers{
			ask officer{
				assert species(violent_offender).name = "rioter";
				do receive_violent_offender(rioter(violent_offender));
			}
		}
		
		list<rioter> perceived_rioters<-length(rioter)=0 ? [] : (rioter at_distance rioter_view_dist);
		loop single_rioter over:perceived_rioters{
			ask single_rioter{
				assert species(violent_offender).name = "rioter";
				do receive_violent_offender(rioter(violent_offender));
			}
		}
		
	}
	
	geometry _shape <- square(0.5);
	
	aspect item_base {
		draw _shape border:#black color:#orange;
	}
}

