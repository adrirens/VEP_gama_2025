/**
* Name: building
* Based on the internal empty template. 
* Author: julien-rsbrg
* Tags: 
*/


model building

import "../../includes/computer_model.gaml"
import "../utils.gaml"
import "./items.gaml"

/////////// Environment /////////// 

species wall parent: obstacle{
	float size;
	float transverse_angle <- rnd(360.0); // the same mod 180
	rgb my_color<-#blue;
	bool display_info<-false;
	
	float margin<-2.0;
	
	point start_point<-{location.x+size/2*cos(transverse_angle),location.y+size/2*sin(transverse_angle)};
	point end_point<-{location.x-size/2*cos(transverse_angle),location.y-size/2*sin(transverse_angle)};
	
	float max_anchor_dist<-nil;
	
	float default_anchor_dist<-size/2+margin;
	
	init {
		if (max_anchor_dist=nil or max_anchor_dist=0){
			create repulsion_anchor with:(location:location,perception_dist:default_anchor_dist);
		} else {
			if (default_anchor_dist>max_anchor_dist){
				point wall_vector<-end_point-start_point;
				point normalized_wall_vector<-{wall_vector.x/size,wall_vector.y/size,0};
				int n_anchors <- (floor(size/max_anchor_dist)+1);
				float new_anchor_dist<-size/n_anchors;
				
				loop i from:0 to:n_anchors-2{
					point anchor_location<-start_point+{(i+1)*new_anchor_dist*normalized_wall_vector.x,(i+1)*new_anchor_dist*normalized_wall_vector.y};
					create repulsion_anchor with:(location:anchor_location,perception_dist:new_anchor_dist, charisma:1000);
				}
			}
		}
		
		ask computer {
			myself.shape <- create_torus_multiline(myself.start_point,myself.end_point);
		}
	}
	
	
	aspect base {
		draw shape color:my_color;
		draw shape wireframe:true color:my_color;
		
		if display_info{
			draw name at:location+{-1,-3} color:#black;
			draw "location:"+string(location with_precision 2) at: location+{3,3} color:#black;
			}
	}
}

species wall_start_end_point parent:obstacle{
	float size;
	rgb my_color<-#blue;
	bool display_info<-true;
	
	float margin<-2;
	
	point start_point; // to give
	point end_point; // to give
	point centroid;
	
	init {
		ask computer{
			myself.centroid <- compute_weighted_avg_points([myself.start_point,myself.end_point],[1,1]);
			myself.centroid <- convert_to_space(myself.centroid,environment_size,environment_size);
		}
		create repulsion_anchor with:(location:centroid,perception_dist:size/2+margin);
		ask computer {
			myself.shape <- create_torus_multiline(myself.start_point,myself.end_point);
			
		}
	}
	
	aspect base {
		draw shape color:my_color;
		
		if display_info{
			draw name at:location+{-1,-3} color:#black;
			draw "location:"+string(location with_precision 2) at: location+{3,3} color:#black;
			}
	}
}

species building_random schedules: []{
	// TODO: building across torus bi shape generation
	
	int n_vertices<-8; // higher than 3
	
	geometry shape;
	float init_angle<-rnd(360.0);
	float radius;
	
	float step_angle<-360.0/n_vertices;
	list L_vertices;
	
	float max_anchor_dist;
	
	init{
		loop i from:0 to:n_vertices-1{
			add [radius*cos(i*step_angle),radius*sin(i*step_angle),0] to:L_vertices;
		}
		matrix vertices<-matrix(L_vertices);
		
		// rotate
		
		matrix rotation_matrix<-matrix([[cos(init_angle),sin(init_angle),0],
										[-sin(init_angle),cos(init_angle),0],
										[0,0,1]]);
		
		vertices<-rotation_matrix.vertices;
		
		// translate
		matrix matLocation <- matrix([[location.x,location.y,location.z]]);
		matrix matOnes <- 1.0 as_matrix({n_vertices,1});
		
		vertices <- vertices + matLocation.matOnes;
		vertices <- transpose(vertices);
		
		loop i from:0 to:n_vertices-1{
			list<float> v <- vertices row_at i;
			list<float> v_next <- vertices row_at ((i+1) mod (n_vertices));
			point loc_start <- {v[0],v[1]};
			point loc_end <- {v_next[0],v_next[1]};
			list<point> wall_vertices <- [loc_start,loc_end];
			point centroid;
			ask computer{
				centroid <- compute_weighted_avg_points(wall_vertices,[1,1]);
				centroid <- convert_to_space(centroid,environment_size,environment_size);
			}
			
			point transverse_vector <- loc_end-loc_start;
			float transverse_angle <- atan2(transverse_vector.y,transverse_vector.x);
			float wall_size <- sqrt(transverse_vector.x^2+transverse_vector.y^2+transverse_vector.z^2);
			
			create wall with:(location:centroid,size:wall_size,transverse_angle:transverse_angle,display_info:false,max_anchor_dist:max_anchor_dist);
		}
		
		L_vertices<-[];
		loop i from:0 to:n_vertices-1{
			add point(vertices row_at i) to: L_vertices;
		}
		shape<-polygon(L_vertices);
	}
	
	
	aspect base {
		draw shape color: #grey;
	}
}


species building schedules: []{
	// TODO: building across torus bi shape generation
		
	list L_vertices; // to give when creating, should be [[x0,y0,z0],[x1,y1,z1],...]
	int n_vertices<-length(L_vertices); 
	float max_anchor_dist;
	
	init{
		matrix vertices<-matrix(L_vertices);
		vertices <- transpose(vertices);
		
		loop i from:0 to:n_vertices-1{
			list<float> v <- vertices row_at i;
			list<float> v_next <- vertices row_at ((i+1) mod (n_vertices));
			point loc_start <- {v[0],v[1]};
			point loc_end <- {v_next[0],v_next[1]};
			list<point> wall_vertices <- [loc_start,loc_end];
			point centroid;
			ask computer{
				centroid <- compute_weighted_avg_points(wall_vertices,[1,1]);
				centroid <- convert_to_space(centroid,environment_size,environment_size);
			}
			
			point transverse_vector <- loc_end-loc_start;
			float transverse_angle <- atan2(transverse_vector.y,transverse_vector.x);
			float wall_size <- sqrt(transverse_vector.x^2+transverse_vector.y^2+transverse_vector.z^2);
			
			create wall with:(location:centroid,size:wall_size,transverse_angle:transverse_angle,display_info:false,max_anchor_dist:max_anchor_dist);
		}
		
		L_vertices<-[];
		loop i from:0 to:n_vertices-1{
			add point(vertices row_at i) to: L_vertices;
		}
		shape<-polygon(L_vertices);
	}
	
	
	aspect base {
		draw shape color: #grey;
	}
}