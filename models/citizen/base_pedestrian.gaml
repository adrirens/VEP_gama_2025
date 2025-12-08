/**
* Name: basepedestrian
* Based on the internal empty template. 
* Author: julien-rsbrg
* Tags: 
*/


model basepedestrian

import "../../includes/computer_model.gaml"
import "../utils.gaml"
import "../unanimate/items.gaml"

/*
 * species with the three rules of the boid flocking algorithm (repulsion, imitation and attraction)
 */
species boid parent:breakable_item skills:[moving]{	
	float charisma <- rnd(P_flocking_charisma_min,P_flocking_charisma_max);
	float sent_dist_imitation <- P_flocking_dist_imitation;
	float sent_dist_attraction <- P_flocking_dist_attraction;
	float sent_dist_repulsion <- P_flocking_dist_repulsion;
	float view_dist <- max(sent_dist_attraction,sent_dist_imitation,sent_dist_repulsion); 
	
	point velocity <- {cos(heading),sin(heading)}*speed update:{cos(heading),sin(heading)}*speed;
	list<boid> agents_flocking_with; // TO GIVE
	
	/*
	 * add (inplace) the repulsion component to the velocity of the boid agent
	 */
	action influence_repulsion(point other_location,float other_charisma,float ratio_efficiency<-10){
		point acc;
		ask computer {
			//write "get vector torus inflkuence repulsion";
			acc <- get_vector_in_torus_perception(origin:other_location,destination:myself.location,max_dist:myself.view_dist);
		}
		acc <- acc*(other_charisma/charisma);
		velocity <- velocity + acc*ratio_efficiency;
	}
	
	/*
	 * add (inplace) the imitation component to the velocity of the boid agent
	 */
	action influence_imitation(point other_velocity, float other_charisma, float ratio_efficiency<-1/100){
		point acc <- other_velocity;
		acc <- acc*(other_charisma/charisma);
		velocity <- velocity + acc*ratio_efficiency;
		
		if focus = self{
			write "";
			write "imitation: acc*ratio_efficiency:"+acc*ratio_efficiency;
		}
	}
	
	/*
	 * add (inplace) the attraction component to the velocity of the boid agent
	 */
	action influence_attraction(point other_location,float other_charisma, float ratio_efficiency<-1/100){
		point acc;
		ask computer {
			//write "get vector torus influence attraction";
			acc <- get_vector_in_torus_perception(origin:myself.location,destination:other_location,max_dist:myself.view_dist);
		}
		acc <- acc*(other_charisma/charisma);
		velocity <- velocity + acc*ratio_efficiency;
		
		if focus = self{
			write "";
			write "attraction: acc*ratio_efficiency:"+acc*ratio_efficiency;
		}
	}
	
	/*
	 * Run the three rules of the boid agent
	 */
	action influence_boid{
		boid closest_boid <- (agents_flocking_with at_distance view_dist) closest_to self;

		if focus = self {
			write "boid influence";
		}
		if closest_boid != nil {
			if self distance_to closest_boid < sent_dist_repulsion {
				do influence_repulsion(closest_boid.location, closest_boid.charisma);
			} else {
				do influence_imitation(closest_boid.velocity, closest_boid.charisma);
				do influence_attraction(closest_boid.location, closest_boid.charisma);
			}
		}
	}
	
	/*
	 * Add the influence of anchors (other species) on the boid agent's movement
	 */
	action influence_anchor {
		//boid closest_boid <- (of_generic_species(agents, anchor) at_distance view_dist) closest_to self;
		repulsion_anchor closest_rep_anchor <- (repulsion_anchor at_distance (speed*step)) closest_to self;
		if focus = self{
			write "";
			write "anchor influence";
		}
		if closest_rep_anchor != nil {
			do influence_repulsion(closest_rep_anchor.location,closest_rep_anchor.charisma);
		} else {
			imitation_anchor closest_imi_anchor <- (imitation_anchor at_distance sent_dist_imitation) closest_to self;
			if closest_imi_anchor != nil {
				do influence_imitation(closest_imi_anchor.velocity,closest_imi_anchor.charisma,1.0);
			}
			attraction_anchor closest_att_anchor <- (attraction_anchor at_distance sent_dist_attraction) closest_to self;
			if closest_att_anchor != nil {
				do influence_attraction(closest_att_anchor.location,closest_att_anchor.charisma,1.0);
			}
		}
	}
	
	geometry free_space;
	/*
	 * Ensures the agent stays in the free space
	 */
	action stay_in_free_space {
		if !(location overlaps free_space){
			point new_location <- (free_space closest_points_with self)[0];
			geometry potential_area <-  polygon([
				new_location + {1,1}*0.1,
				new_location + {-1,1}*0.1,
				new_location + {-1,-1}*0.1,
				new_location + {1,-1}*0.1]);
			new_location <- any_location_in(potential_area - (potential_area - free_space));
			heading <- (location towards new_location);
			location <- new_location;
		}
	}
	
	/*
	 * Move the agent while ensuring the agent stays in the free space
	 */
	action move_in_free_space{		
		point temp_location <- location+velocity*speed/norm(velocity);
		ask computer {
			temp_location  <- convert_to_space(temp_location );
		}
		location <- temp_location ;
				
		do stay_in_free_space;
	}
	
	/*
	 * Run the complete boid agent's movement
	 */
	action flock{
		do influence_boid;
		do influence_anchor;
		
		do move_in_free_space;
	}
	
	float size <- 0.5#m;
	float shape_angle <- 120.0;
	rgb my_color <- #blue;
	geometry arrow_shape {
		point X_head<-{size*cos(heading),size*sin(heading)}+location;
		point X_back_left<-{size*cos(heading+shape_angle),size*sin(heading+shape_angle)}+location;
		point X_back_right<-{size*cos(heading-shape_angle),size*sin(heading-shape_angle)}+location;
		return polygon([X_head,X_back_left,location,X_back_right]);
	}
	
	aspect default {
		draw arrow_shape() color: my_color;
		//draw circle(view_dist) wireframe:true color:#black;
	}
}


