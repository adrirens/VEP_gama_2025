/**
* Name: computermodel
* Based on the internal empty template. 
* Author: julien-rsbrg
* Tags: 
*/


model computermodel


// abstract species used as a library of complex computations
species computer schedules: []{
	float environment_size; // TO GIVE
	
	/*
	 * Compute the average of the points weighted by the weights associated by index
	 * Careful: to not use directly in torus 
	 */
	point compute_weighted_avg_points(list<point> all_points, list<float> weights){
		point centroid<-{0,0};
		loop i from: 0 to: length(all_points)-1{
			centroid <- centroid+all_points[i]*weights[i];
		}
		centroid <- centroid/sum(weights);
		return centroid;
	}
	
	/*
	 * Compute the average of the angles weighted by the weights associated by index
	 */
	float compute_average_angles(list<float> all_angles, list<float> weights){
		list<point> all_vectors;
		loop angle over: all_angles{
			point new_vector <- {cos(angle),sin(angle)};
			add new_vector to:all_vectors;
		}		
		point avg_vector <- compute_weighted_avg_points(all_vectors,weights);
		return atan2(avg_vector.y,avg_vector.x);
	}
	
	
	/*
	 * Get the shortest vector from origin to destination considering the world as a torus
	 */
	point get_vector_in_torus_optimization (point origin, point destination, float env_length_x<-environment_size, float env_length_y<-environment_size){
		// augment the lists into matrices
		list<list<float>> potential_destinations;
		loop x_added over:[-env_length_x,0,env_length_x]{
			loop y_added over:[-env_length_y,0,env_length_y]{
				add list(destination+{x_added,y_added}) to:potential_destinations;
			}
		}
		matrix augmented_destination <- matrix(potential_destinations);
		
		matrix augmented_origin <- matrix([[origin.x,origin.y,origin.z]]);
		matrix matOnes <- 1.0 as_matrix({9,1});
		augmented_origin <- augmented_origin.matOnes;
		
		// Compute distances
		matrix matOnes <- 1.0 as_matrix({3,1});
		matrix distances <- augmented_destination-augmented_origin;
		distances <- distances*distances;
		distances <- matOnes.distances;
		
		// Keep min distance location
		float min_dist<-1e9;
		int id_min<-nil;
			
		loop id_candidate_dist from:0 to:8{
			float candidate_dist<-distances[id_candidate_dist];
			if (candidate_dist < min_dist){
				min_dist<-candidate_dist;
				id_min<-id_candidate_dist;
			}
		}
		point torus_destination<-point(potential_destinations[id_min]);
		
		
		return torus_destination-origin;
	}
	
	/*
	 * Get the shortest vector from origin to destination considering the world as a torus.
	 * Optimized when the maximum distance between the origin and destination are known
	 */
	point get_vector_in_torus_perception (point origin, point destination, float max_dist, float env_length_x<-environment_size, float env_length_y<-environment_size){
		point result_vector <- destination - origin;
		float x_value <- result_vector.x;
		float y_value <- result_vector.y;
		if (x_value < -max_dist){
			x_value <- x_value + env_length_x;
		} else if (x_value > max_dist){
			x_value <- x_value - env_length_x;
		}
		if (y_value < -max_dist){
			y_value  <- y_value  + env_length_y;
		} else if (y_value  > max_dist){
			y_value  <- y_value - env_length_y;
		}
		result_vector <- {x_value,y_value};
		return result_vector;
	}
	
	
	/*
	 * Relocate (not inplace) the point called 'sampled_point' in the bounded environment by succcessive shifts
	 */
	point convert_to_space (point sampled_point, float env_length_x<-environment_size, float env_length_y<-environment_size){
		float x_value <- sampled_point.x;
		float y_value <- sampled_point.y;
		
		loop while: (x_value<0){
			x_value <- x_value+env_length_x;
		}
		
		loop while: (x_value>env_length_x){
			x_value <- x_value-env_length_x;
		}
		
		loop while: (y_value<0){
			y_value <- y_value+env_length_y;
		}
		
		loop while: (y_value>env_length_y){
			y_value <- y_value-env_length_y;
		}
		
		point relocation <- {x_value,y_value};
		return relocation;
	}
	
	/*
	 * Compute the L2 norm
	 */
	float compute_l2_norm(point vector){
		// can also copy paste it
		return sqrt(vector.x^2+vector.y^2+vector.z^2);
	}
	
	/*
	 * Check that test_point belongs to the quadrant defined with center start_point and to which end_point belongs
	 */
	bool is_in_same_quadrant_from_start_as_end(point start_point,point end_point, point test_point){
		bool same_x_halfplane<-((test_point.x>=start_point.x) and (end_point.x>=start_point.x)) or ((test_point.x<=start_point.x) and (end_point.x<=start_point.x));
		bool same_y_halfplane<-((test_point.y>=start_point.y) and (end_point.y>=start_point.y)) or ((test_point.y<=start_point.y) and (end_point.y<=start_point.y));
		return (same_x_halfplane and same_y_halfplane);
	}
	
	/*
	 * Return the vector necessary to relocate sampled_point in the bounded environment
	 */
	point compute_shift_to_environment(point sampled_point, point xy_min<-{0,0}, point xy_max<-{environment_size,environment_size}){
		float x_min<-xy_min.x;
		float y_min<-xy_min.y;
		float x_max<-xy_max.x;
		float y_max<-xy_max.y;
		
		float env_length_x<-x_max-x_min;
		float env_length_y<-y_max-y_min;
		assert env_length_x > #min_float;
		assert env_length_y > #min_float;
		
		point shift <- {0.0,0.0,0.0};
		point new_sampled_point <- copy(sampled_point);
		loop while: (new_sampled_point.x<x_min){
			shift <- shift + {env_length_x,0.0};
			new_sampled_point <- copy(sampled_point)+shift;
		}
		
		loop while: (new_sampled_point.x>x_max){
			shift <- shift - {env_length_x,0.0};
			new_sampled_point <- copy(sampled_point)+shift;
		}
		
		loop while: (new_sampled_point.y<y_min){
			shift <- shift + {0.0,env_length_y};
			new_sampled_point <- copy(sampled_point)+shift;
		}
		
		loop while: (new_sampled_point.y>env_length_y){
			shift <- shift - {0.0,env_length_y};
			new_sampled_point <- copy(sampled_point)+shift;
		}
		
		return shift;
	}
	
	/*
	 * Check point_to_probe respects the boundaries of the torus
	 */
	bool is_point_in_torus(point point_to_probe, point xy_min<-{0,0}, point xy_max<-{environment_size,environment_size}){
		return point_to_probe.x>=xy_min.x and point_to_probe.x<=xy_max.x and point_to_probe.y>=xy_min.y and point_to_probe.y<=xy_max.y;
		}
		
	/*
	 * Create a line that can cross the torus world from one side to the symmetric one.
	 * 
	 * The multiline is the minimal line to draw. If it overlaps itself, it will be simplified.
	 */
	geometry create_torus_multiline(point start_point, point end_point, point xy_min<-{0,0}, point xy_max<-{environment_size,environment_size}){
		
		point shift_to_env <- compute_shift_to_environment(start_point,xy_min,xy_max);
		list<point> line_corrected <- translate([start_point,end_point],shift_to_env);
		start_point<-line_corrected[0];
		end_point<-line_corrected[1];
		
		float x_min<-xy_min.x;
		float y_min<-xy_min.y;
		float x_max<-xy_max.x;
		float y_max<-xy_max.y;
		
		bool start_point_in_env <- is_point_in_torus(point_to_probe:start_point,xy_min:xy_min,xy_max:xy_max);
		bool end_point_in_env <- is_point_in_torus(point_to_probe:end_point,xy_min:xy_min,xy_max:xy_max);
		if (start_point_in_env and end_point_in_env){
			return line([start_point,end_point]);
		}
		float x_length<-(x_max-x_min);
		float y_length<-(y_max-y_min);
		
		float line_length<-norm(end_point-start_point);
		bool null_delta_x <- abs(end_point.x-start_point.x) < #min_float;
		assert !(null_delta_x and abs(end_point.y-start_point.y) < #min_float) label:"some points are too close";
		
		float alpha;
		float beta;
		if null_delta_x {
			alpha <- 0.0;
			beta <- start_point.y;			
		} else {
			alpha <- (end_point.y-start_point.y)/(end_point.x-start_point.x);
			beta <--alpha*start_point.x+start_point.y;
		}
			
		point first_point_intersect<-end_point;
		float d_min <- 2*line_length;
		float d_is_at_min <- line_length;
		
		if !null_delta_x {
			loop x_i over:[x_min,x_max]{			
				float y_i <- alpha*x_i+beta;
				
				float d_is <- norm({x_i,y_i}-start_point);
				float d_ie <- norm({x_i,y_i}-end_point);
				float d_i <- d_is+d_ie;
				if (d_i<d_min and d_is<=d_is_at_min and d_is>1e-6 and is_in_same_quadrant_from_start_as_end(start_point,end_point,{x_i,y_i})){
					d_min<-d_i;
					d_is_at_min<-d_is;
					first_point_intersect<-{x_i,y_i};
				}
			}
		}
		
		
		loop y_i over:[y_min,y_max]{
			float x_i;
			if null_delta_x {
				x_i <- beta;
			} else {
				x_i <- alpha*y_i+beta;
			}
			
			float d_is <- norm({x_i,y_i}-start_point);
			float d_ie <- norm({x_i,y_i}-end_point);
			float d_i <- d_is+d_ie;
			
			if (d_i<d_min and d_is<=d_is_at_min and d_is>1e-6 and is_in_same_quadrant_from_start_as_end(start_point,end_point,{x_i,y_i})){
				d_min<-d_i;
				d_is_at_min<-d_is;
				first_point_intersect<-{x_i,y_i};
			}		
		}		
		
		if (d_is_at_min>=line_length){
			return line([start_point,end_point]);
		} else {
			point shift <- {0.0,0.0};
			if (first_point_intersect.x=x_min){
				shift <- shift + {x_length,0};
			} 
			if (first_point_intersect.x=x_max){
				shift <- shift - {x_length,0};
			} 
			if (first_point_intersect.y=y_min){
				shift <- shift + {0,y_length};
			} 
			if (first_point_intersect.y=y_max){
				shift <- shift - {0,y_length};
			}
			geometry multiline <- line([start_point,first_point_intersect]);
			point new_end_point <- translate([end_point],shift)[0];
			point new_point_intersect <- translate([first_point_intersect],shift)[0];
			if norm(new_end_point-new_point_intersect)<=1e-8{
				return multiline;
			} else {
				return multiline + create_torus_multiline(new_point_intersect,new_end_point,xy_min,xy_max);
			}
		}
	}
	
	
	/*
	 * Reconstruct a single straight line from a multilinestring that was a single line cut to fit a torus world. 
	 * Stop the reconstruction when two consecutive points in the line are too distant to each other.
	 */
	geometry reconstruct_torus_line(geometry torus_multiline, point xy_min<-{0,0}, point xy_max<-{environment_size,environment_size}){
		list<point> all_points <- torus_multiline.geometries accumulate each.points;
		
		float env_length_x<-xy_max.x-xy_min.x;
		float env_length_y<-xy_max.y-xy_min.y;
		assert env_length_x > #min_float;
		assert env_length_y > #min_float;
		
		ask computer {
			point shift_to_env;
			shift_to_env <- compute_shift_to_environment(all_points[0],xy_min,xy_max);
			all_points <- translate(all_points,shift_to_env);
		}
		
		int n_points <- length(all_points);
		assert n_points mod 2 = 0 label:(string(n_points)+ " mod 2 ="+(n_points mod 2)+"!=0 -- "+all_points);
		
		point shift_to_apply_end_point <- {0.0,0.0};
		point local_shift;
		bool disconnected_line <- false;
		
		point point_to_probe;
		point shifted_next_point;
		int i <- 1;
		loop while: i < n_points-1 and !disconnected_line{
			point_to_probe <- all_points[i];
			local_shift <- {0.0,0.0};
			if abs(point_to_probe.x - xy_min.x) < #min_float {
				local_shift <- local_shift - {env_length_x,0.0};
			}
			
			if abs(point_to_probe.x - xy_max.x) < #min_float {
				local_shift <- local_shift + {env_length_x,0.0};
			}
			
			if abs(point_to_probe.y - xy_min.y) < #min_float {
				local_shift <- local_shift - {0.0,env_length_y};
			}
			
			if abs(point_to_probe.y - xy_max.y) < #min_float {
				local_shift <- local_shift + {0.0,env_length_y};
			}
			
			ask computer {
				shifted_next_point <- translate([all_points[i+1]],local_shift)[0];
			}
			if abs(norm(shifted_next_point-point_to_probe)) > #min_float{
				disconnected_line <- true;
			}
			
			shift_to_apply_end_point <- shift_to_apply_end_point + local_shift;

			i <- i + 2; 
		}
		
		point end_point;
		ask computer {
			if disconnected_line{
				end_point <- translate([point_to_probe],shift_to_apply_end_point)[0];
			} else {
				end_point <- translate([all_points[n_points-1]],shift_to_apply_end_point)[0];
			}
			
		}
		
		return line([all_points[0],end_point]);
	}
	
	/*
	 * Compute the sigmoid
	 */
	float compute_sigmoid(float x){
		return 1/(1+exp(-x));
	}
	
	/*
	 * Remove (not inplace) every pair with key key_to_remove in initial_map
	 */
	map<unknown,unknown> remove_pair_with_key(map<unknown,unknown> initial_map,unknown key_to_remove){
		map new_map;
		loop key over: initial_map.keys{
			if (key != key_to_remove) {
				add key::initial_map[key] to: new_map;
			}
		}
		return new_map;
	}
	
	/*
	 * Compute the average of the points in locations that belong to a torus with origin base_location
	 * The average is weighted by the weights list
	 */
	point compute_avg_location_torus(point base_location, list<point> locations, list<float> weights, float env_length_x<-environment_size, float env_length_y<-environment_size){
		// augment the lists into matrices
		list<list<list<float>>> L_augmented_locations;
		loop single_location over:locations{
			list<list<float>> local_augmented_locations;
			loop x_added over:[-env_length_x,0,env_length_x]{
				loop y_added over:[-env_length_y,0,env_length_y]{
					add list(single_location+{x_added,y_added}) to:local_augmented_locations;
				}
			}
			add local_augmented_locations to:L_augmented_locations;
		}
		
		matrix augmented_base_location <- matrix([[base_location.x,base_location.y,base_location.z]]);
		matrix matOnes <- 1.0 as_matrix({9,1});
		augmented_base_location <- augmented_base_location.matOnes;
		
		// Compute distances
		list<matrix<float>> all_potential_distances;
		matrix matOnes <- 1.0 as_matrix({3,1});
		loop i from:0 to:length(locations)-1{
			matrix<float> augmented_locations <- matrix(L_augmented_locations[i]);
			matrix dist <- augmented_locations-augmented_base_location;
			dist <- dist*dist;
			dist <- matOnes.dist;
			add dist to: all_potential_distances;
		}
		
		// Keep min distance location
		list<point> torus_locations;
		
		float min_dist;
		int id_min;
		loop id_location from:0 to:length(locations)-1{
			matrix one_location_distances<-all_potential_distances[id_location];
			
			min_dist<-1e9;
			id_min<-nil;
			
			loop id_candidate_dist from:0 to:8{
				float candidate_dist<-one_location_distances[id_candidate_dist];
				if (candidate_dist < min_dist){
					min_dist<-candidate_dist;
					id_min<-id_candidate_dist;
				}
			}
			add point(L_augmented_locations[id_location][id_min]) to:torus_locations;
		}
		
		// Compute average and covert to space
		point mean_location <- compute_weighted_avg_points(torus_locations, weights);
		mean_location <- convert_to_space(mean_location, env_length_x, env_length_y);
		
		return mean_location;
	}
	
	/*
	 * Create a part of a circle geometry
	 */
	geometry create_part_circle(point center_location, float complete_angle, float init_angle, int n_vertices, float radius){
		assert complete_angle>0;
		assert complete_angle<360;
		
		assert n_vertices>=2;
		
		float step_angle <- complete_angle/(n_vertices-1);
		list<list<float>> L_vertices;
		list<point> point_L_vertices;
		geometry part_circle_shape;
		
		loop i from:0 to:n_vertices-1{
			add [radius*cos(i*step_angle),radius*sin(i*step_angle),0] to:L_vertices;
		}
		add [0.0,0.0,0.0] to:L_vertices;
		
		matrix vertices<-matrix(L_vertices);
		
		// rotate
		
		matrix rotation_matrix<-matrix([[cos(init_angle),sin(init_angle),0],
										[-sin(init_angle),cos(init_angle),0],
										[0,0,1]]);
		
		vertices<-rotation_matrix.vertices;
		
		// translate
		matrix matLocation <- matrix([[center_location.x,center_location.y,center_location.z]]);
		matrix matOnes <- 1.0 as_matrix({n_vertices+1,1});
		
		vertices <- vertices + matLocation.matOnes;
		vertices <- transpose(vertices);
		
		point_L_vertices<-[];
		loop i from:0 to:n_vertices{
			add point(vertices row_at i) to: point_L_vertices;
		}
		part_circle_shape <- polygon(point_L_vertices);
		
		return part_circle_shape;
	}
	
	/*
	 * Create n_subdivisions nonoverlapping 2d cones around origin_location of radius perception_distance
	 * ---
	 * (One of the cone has one of its segments with angle init_angle)
	 */
	list<geometry> create_perception_subdivisions(int n_subdivisions, point origin_location, float perception_distance,  float init_angle<-rnd(360.0)){
		float angle_per_subdivision <- 360.0/n_subdivisions;
		list<geometry> subdivisions <- [];
		loop i from:0 to:n_subdivisions-1{
			add create_part_circle(
				center_location:origin_location, 
				complete_angle:angle_per_subdivision, 
				init_angle:init_angle+i*(angle_per_subdivision), 
				n_vertices:5, 
				radius:perception_distance
			) to:subdivisions;
		}
		return subdivisions;
	}
	
	/*
	 * Check that the agent located at origin_location is surrounded 
	 * (ie when n_subdivisions_to_surround subdivisions of the n_subdivisions part circles drawn around are overlapping with obstacles)
	 * init_angle is used as the starting angle to draw the part circles constituting the divisions
	 * perception_distance is the radius of those part circles
	 */
	bool is_surrounded(list<agent> obstacles, int n_subdivisions_to_surround, int n_subdivisions, point origin_location, float perception_distance, float init_angle<-rnd(360.0)){
		list<geometry> subdivisions <- create_perception_subdivisions(
			n_subdivisions:n_subdivisions, 
			origin_location:origin_location, 
			perception_distance:perception_distance, 
			init_angle:init_angle
		);
		
		int n_subdivs_taken;
		loop subdiv over: subdivisions{
			if !(empty(obstacles overlapping subdiv)){
				n_subdivs_taken <- n_subdivs_taken + 1;
			}
		}
		
		return n_subdivs_taken >= n_subdivisions_to_surround;
	}
	
	/*
	 * Rotate all the locations of L_locations by 'angle' around 'origin'
	 */
	list<point> rotate(list<point> L_locations, float angle, point origin){
		list<point> new_L_locations <- translate(L_locations, -origin);
		new_L_locations<-new_L_locations accumulate [{
			each.x*cos(angle)-each.y*sin(angle), // inversed orientation
			each.x*sin(angle)+each.y*cos(angle),
			each.z
		}];
		new_L_locations <- translate(new_L_locations, origin);
		return new_L_locations;
	}
	
	/*
	 * Apply a translation to all the locations of L_locations of 'shift'
	 */
	list<point> translate(list<point> L_locations, point shift){
		list<point> new_L_locations<-L_locations accumulate [each + shift];
		return new_L_locations;
	}
	
	/*
	 * create a regular polygons of n_points
	 */
	list<point> create_regular_shape(int n_points, float radius){
		list<point> res;
		
		float step_angle<-(n_points>0)? 360.0/n_points:0.0;
		
		loop i from:0 to:n_points-1{
			add {int(n_points>1)*radius*cos(i*step_angle),
				 int(n_points>1)*radius*sin(i*step_angle),
				 0.0
				} to:res;
		}
		return res;
	}
	
	
	/*
	 * Optimally fill the area defined by the box_dimensions with n_elems of elem_dimensions dimensions and minimal interspace between them
	 * 
	 * Returns a warning if impossible
	 * 
	 * box_dimensions, elem_dimensions have format [x_size, y_size]
	 * min_interspace_dimensions has format [x_min,y_min]
	 */
	list<point> optimize_fill(list<float> box_dimensions, int n_elems, list<float> elem_dimensions, list<float> min_interspace_dimensions){
		assert n_elems > 0;
		
		int n_rows <- 1;
		int n_elems_per_row <- 1;
		
		list<float> curr_interspace_dim <- [min_interspace_dimensions[0],min_interspace_dimensions[1]];
		
		int i_check_even;
		loop while: n_rows*n_elems_per_row < n_elems and curr_interspace_dim[0] >= min_interspace_dimensions[0] and curr_interspace_dim[1] >= min_interspace_dimensions[1]{
			if (i_check_even mod 2) = 0 {
				n_elems_per_row <- n_elems_per_row + 1;
			} else {
				n_rows <- n_rows + 1;
			}
			curr_interspace_dim <- [box_dimensions[0]/n_elems_per_row - elem_dimensions[0], box_dimensions[1]/n_rows - elem_dimensions[1]];
			
			i_check_even <- i_check_even+1;
		}
		
		if n_rows*n_elems_per_row < n_elems {
			write 'WARNING: impossible to fill the elements. Consider allowing lower interspace sizes';
			write "n_rows, n_elems_per_row : " + n_rows + ", "+ n_elems_per_row;
			write "n_rows*n_elems_per_row <  n_elems?" + n_rows*n_elems_per_row + " < "+ n_elems+ " ?";
			write "curr_interspace_dim[0] >= bounds_interspace_dimensions[0] :" +curr_interspace_dim[0] + ">=" + min_interspace_dimensions[0];
			write "curr_interspace_dim[1] >= bounds_interspace_dimensions[1] :" +curr_interspace_dim[1] + ">=" + min_interspace_dimensions[1];
			return [];
		}
		
		
		list<point> res;
		loop i_elem from: 0 to: n_elems-1 {
			int i_row <- i_elem div n_elems_per_row;
			int j_col <- i_elem mod n_elems_per_row;
			
			if i_row = n_rows-1 {
				j_col <- j_col + ((n_rows*n_elems_per_row - n_elems) div 2);
			}
			
			point new_location <- {
				(j_col+1)*(elem_dimensions[0]/2+curr_interspace_dim[0])+j_col*elem_dimensions[0]/2-curr_interspace_dim[0]/2,
				(i_row+1)*(elem_dimensions[1]/2+curr_interspace_dim[1])+i_row*elem_dimensions[1]/2-curr_interspace_dim[1]/2
			};
			add new_location to: res;
		}
		
		
		return res;
	} 
	
	/*
	 * create an oriented arrow shape 
	 */
	geometry directed_arrow(point start_point,point end_point){
   		point end_to_start <- start_point - end_point;
   		end_to_start <- end_to_start/norm(end_to_start);
   		
   		point base_corner_a;
   		point base_corner_b;
   		
   		ask computer {
   			point ortho_end_to_start <- rotate([end_to_start], 90.0, {0.0,0.0})[0];
   			base_corner_a <- translate([end_point], end_to_start+ortho_end_to_start/2)[0];
   			base_corner_b <- translate([end_point], end_to_start-ortho_end_to_start/2)[0];
   		}
   		
   		geometry head <- polygon([
   			end_point,
   			base_corner_a,
   			base_corner_b
   		]);
   		return line([start_point,end_point])+head;
   	}
}
