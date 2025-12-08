/**
* Name: MoussaidModel
* Description: Pedestrian model proposed by: "Moussaïd, M., Helbing, D., & Theraulaz, G. (2011). 
* How simple rules determine pedestrian behavior and crowd disasters. Proceedings of the National Academy of Sciences, 108(17), 6884-6888."
* Based on the internal skeleton template. 
* Author: Patrick Taillandier
* Tags: Pedestrian
*/

model MoussaidModel

import "../models/unanimate/building.gaml"
import "../models/unanimate/items.gaml"
import "./common_global.gaml"


species basic_pedestrian parent:breakable_item skills:[moving]{
	bool automove <- false;
	
	rgb color <- rnd_color(255);
	point o;
	float v0 <- gauss(P_v0_mean, P_v0_std);
	float tau <- 1.0;
	float alpha0;
	point acc<- {0,0};
	point vi <- {0,0};
	
	geometry free_space;
	bool is_torus<-nil; // TO GIVE
	
	user_command focus {
		focus <- self;
	}
	
	init {
		assert is_torus != nil;
		
		if !is_torus{
			heading <- location towards o;
		} else {
			ask computer {
				point vector_loc_to_o <- get_vector_in_torus_optimization(origin:myself.location, destination:myself.o);
				myself.heading <- atan2(vector_loc_to_o.y,vector_loc_to_o.x);
			}
		}
		
		//write "basic_pedestrian free_space:"+free_space;
	}
	
	action move_to(point o) {
		if focus=self {write name+"move_to:"+o;}
		
		float dist_o;
		if !is_torus{
			dist_o <- location distance_to o;
			alpha0 <- location towards o;
		} else {
			ask computer {
				point vector_loc_to_o <- get_vector_in_torus_optimization(origin:myself.location, destination:o);
				dist_o <- norm(vector_loc_to_o);
				myself.alpha0 <- atan2(vector_loc_to_o.y,vector_loc_to_o.x);
			}
		}
		
		heading <- alpha0;
		do manage_move(dist_o);		
	}
	
	action move_away_from(point o){
		point retreat_vector; 
		if !is_torus{
			retreat_vector <- location - o;
		} else {
			ask computer {
				retreat_vector <- get_vector_in_torus_optimization(origin:o, destination:myself.location);
			}
		}
		retreat_vector <- retreat_vector/norm(retreat_vector)*(v0*tau); // v0*tau so that it does not slow down
		point opposite_o <- retreat_vector + location;
		do move_to(opposite_o);
	}
	
	reflex move_pedestrian {
		if automove {
			do move_to(o);
		}
	}
	
	action stay_in_free_space {
		if !(location overlaps free_space){
			location <- (free_space closest_points_with self)[0];
		}
	}
	
	action manage_move (float dist_o) {
		float vdes <-  min(v0,dist_o/tau);
		if self = focus {
			write name + " o ="+ o +" vdes "+ vdes;
		}
		point vdes_vector <-  {cos(heading), sin(heading)};
		vdes_vector <- vdes_vector * vdes;
		acc <- (vdes_vector - vi)/ tau;
		vi <- vi + (acc * step);
		speed <- norm(vi);
		heading <- atan2(vi.y,vi.x);
		do move;
		do stay_in_free_space;
	}
}

species pedestrian parent: breakable_item skills:[moving]{ // TODO: torus with moving
	bool automove <- false;
	
	float m <- rnd(60.0,100.0);
	float shoulder_length <- m/320.0#m;
	geometry shape <- circle(shoulder_length);
	rgb color <- rnd_color(255);
	point o;
	float v0 <- gauss(P_v0_mean, P_v0_std);
	float teta0 <- P_teta0; //degrees
	float tau <- P_tau;
	float dmax <- P_dmax;
	float disc_factor <- P_disc_factor;
	float k <- P_k;
	float alpha0;
	float v;
	float dh; // f_alpha associated with the min d_alpha
	list<geometry> visu_ray; // where the agents can see with obstacles' obstructions accounted for
	list<float> val_angles; // list of angles of the casted vision rays
	float heading;
	point acc<- {0,0};
	point vi <- {0,0};
	float c; // sum of the norms of the force exerted on agent => to compute compression
	
	bool is_torus<-nil; // TO GIVE
	
	user_command focus {
		focus <- self;
	}
	
	init {
		assert is_torus != nil;
		
		int num <- int(2 * teta0 / disc_factor);
		if !is_torus{
			heading <- location towards o;
		} else {
			ask computer {
				point vector_loc_to_o <- get_vector_in_torus_optimization(origin:myself.location, destination:myself.o);
				myself.heading <- atan2(vector_loc_to_o.y,vector_loc_to_o.x);
			}
		}
		loop i from: 0 to: num {
			val_angles <<  ((i * disc_factor) - teta0);
		}
	}
	
	action move_to(point o) {
		if focus=self {write name+"move_to:"+o;}
		c <- 0.0;
		
		float dist_o;
		if !is_torus{
			dist_o <- location distance_to o;
			alpha0 <- location towards o;
		} else {
			ask computer {
				point vector_loc_to_o <- get_vector_in_torus_optimization(origin:myself.location, destination:o);
				dist_o <- norm(vector_loc_to_o);
				myself.alpha0 <- atan2(vector_loc_to_o.y,vector_loc_to_o.x);
			}
		}
		
		visu_ray <- [];
		dh <- #max_float;
		float dmin <- #max_float;
		
		float h0 <- copy(heading);
		
		loop a over: val_angles {
			float alpha <- a + h0;
			list<float> r <- compute_distance(alpha,min(dist_o,dmax));
			
			if self = focus {
				write name + " " + alpha + " " + r +  " " + alpha0 + " " + cos(alpha0 - alpha);
			}
			float d_alpha <- r[0];
			if (d_alpha < dmin ) {
				dmin <- d_alpha;
				dh <- r[1];
				heading <- alpha;
			}
		}
		do manage_move(dist_o);		
	}
	
	action move_away_from(point o){
		point retreat_vector; 
		if !is_torus{
			retreat_vector <- location - o;
		} else {
			ask computer {
				retreat_vector <- get_vector_in_torus_optimization(origin:o, destination:myself.location);
			}
		}
		retreat_vector <- retreat_vector/norm(retreat_vector)*(v0*tau); // v0*tau so that it does not slow down
		point opposite_o <- retreat_vector + location;
		do move_to(opposite_o);
	}
	
	reflex move_pedestrian {
		if automove {
			do move_to(o);
		}
	}
	
	list<float> compute_distance (float alpha, float dist_o){
		// distance to travel to reach destination by taking angle alpha
		float f_alpha <- f(alpha, dist_o);
		
		return [dist_o ^2 + f_alpha ^2 - 2 * dist_o *f_alpha * cos(alpha0 - alpha), f_alpha];
	}
	
	point force_repulsion_wall(wall w) {
		if (location intersects w) {
			float strength <- k * shoulder_length ;
			point pt_w <- (w.shape.contour closest_points_with location)[0]; // ok for torus: already intersects anyway
			point vv <- {pt_w.x - location.x ,pt_w.y - location.y };
			float n <- norm(vv);
			return vv * (strength/n); 
		} else {		
			float strength <- k * (shoulder_length - (location distance_to w)); // TODO: not ok for torus
			c <- c + strength;
			point pt_w <- (w closest_points_with location)[0];
			point vv <- {location.x - pt_w.x,location.y - pt_w.y };
			float n <- norm(vv);
			return vv * (strength/n); 
		}
	}
	point force_repulsion(pedestrian other) {
		float dist_other;
		point vv;
		if !is_torus{
			dist_other <- location distance_to other.location;
			vv <- {location.x - other.location.x, location.y - other.location.y};
		} else {
			ask computer {
				vv <- get_vector_in_torus_optimization(origin:other.location, destination:myself.location);
				dist_other <- norm(vv);
			}
		}
		
		float strength <- k * (other.shoulder_length + shoulder_length - dist_other);
		c <- c + strength;
		return vv * (strength/dist_other); 
	}
	
	
	float f(float alpha,float dmax_r) {
		geometry line;
		if !is_torus{
			line <- line([location, location + ({cos(alpha), sin(alpha)} * dmax_r)]);
		} else {
			ask computer {
				line <- create_torus_multiline(start_point:myself.location, end_point:myself.location + {cos(alpha), sin(alpha)} * dmax_r);
			}
		}
		
		list<pedestrian> ps <- (pedestrian overlapping line)  - self;
		list<wall> ws <- wall overlapping line;
		
		if self = focus {
				//write name + " ws " + ws;
			}
		
		loop w over: ws {
			line <- line - w; // returns a multilinestring of segments of line deprived of the shape of w
			if line = nil {return 0.0;}
		}
		loop p over: ps {
			line <- line - p;
			if line = nil {return 0.0;}
		}
		
		if !is_torus{
			line <- line.geometries first_with (location in each.points); // only keep the segment where the agent is on
		} else {
			if line.perimeter = 0 {
					return 0.0;
				}
			ask computer {
				line <- reconstruct_torus_line(line);
			}
		}
		line <- line - self;
		if line = nil {
			return 0.0;
		}
		if display_field_vision {
			point disp_start <- (line.geometries accumulate each.points)[0];
			point disp_end <- (line.geometries accumulate each.points)[1];
			ask computer {
				line <- create_torus_multiline(start_point:disp_start, end_point:disp_end);
			}
			
			visu_ray << line;
		}
		return line.perimeter;	// length of the line
	}
	
	point compute_sf_pedestrian {
		point sf <- {0.0,0.0};
		loop p over: (pedestrian overlapping self) - self {
			sf <- sf + force_repulsion(p);
		}
		
		return sf/m;
	}
	
	point compute_sf_wall {
		point sf <- {0.0,0.0};
		loop w over: wall overlapping self{
			sf <- sf + force_repulsion_wall(w);
		}
		
		return sf/m;
	}
	
	action manage_move (float dist_o) {
		float vdes <-  min(v0, dh/tau);
		if self = focus {
			write name + " o ="+ o +" vdes "+ vdes + " dh/tau="+dh/tau;
		}
		point vdes_vector <-  {cos(heading), sin(heading)};
		vdes_vector <- vdes_vector * vdes;
		acc <- (vdes_vector - vi)/ tau +  compute_sf_pedestrian() +  compute_sf_wall();
		vi <- vi + (acc * step);
		speed <- norm(vi);
		heading <- atan2(vi.y,vi.x);
		do move;
	}
	
	aspect default {	
		if display_field_vision {
			loop l over: visu_ray {
				draw l color: color;
			}
		}
	
		draw  circle(shoulder_length) rotate: heading + 90.0 color: color;
	}
}
