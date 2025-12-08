/**
* Name: tools
* Based on the internal empty template. 
* Author: julien-rsbrg
* Tags: 
*/


model utils

species arrow_display {
	float charisma <- rnd(1.0);
	
	float size;
	float shape_angle;
	rgb my_color;
	float heading<-rnd(360.0);
	
	geometry basic_shape (float size, float shape_angle){
		point X_head<-{size*cos(heading),size*sin(heading)}+location;
		point X_back_left<-{size*cos(heading+shape_angle),size*sin(heading+shape_angle)}+location;
		point X_back_right<-{size*cos(heading-shape_angle),size*sin(heading-shape_angle)}+location;
		return polygon([X_head,X_back_left,location,X_back_right]);
	}
	
	aspect base {
		draw basic_shape(size,shape_angle) color: my_color;
	}
	
	
	
}

species anchor parent:arrow_display{
	float charisma <- 100.0;
	float size <- 2.0;
	float shape_angle <- 160.0;
	rgb my_color;
	
	float perception_dist<-8.0;
	
	float heading<-rnd(360.0);
	point velocity <- {cos(heading),sin(heading)};
	
	geometry basic_shape (float size, float shape_angle){
		point X_head<-{size*cos(heading),size*sin(heading)}+location;
		point X_back_left<-{size*cos(heading+shape_angle),size*sin(heading+shape_angle)}+location;
		point X_back_right<-{size*cos(heading-shape_angle),size*sin(heading-shape_angle)}+location;
		return polygon([X_head,X_back_left,location,X_back_right]);
	}
	
	aspect base {
		draw basic_shape(size,shape_angle) color: my_color;
	}
	
	aspect info {
		draw circle(perception_dist) color: my_color wireframe: true;
	}
}

species imitation_anchor parent:anchor{
	rgb my_color<-#black;
}

species attraction_anchor parent:anchor{
	rgb my_color<-#green;
}

species repulsion_anchor parent:anchor{
	rgb my_color<-#red;
	
	// destroy arrow_display for this one
	geometry basic_shape (float size, float shape_angle){
		return circle(size/2);
	}
	
	aspect base {
		draw basic_shape(size,shape_angle) color: my_color;
	}
}