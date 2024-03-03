/* Maze
 * Author: Shivangi Shah
 * Creation date: 17-Dec-22
 */
MACHINE
    Maze
    
CONSTANTS
    x_axis, //Defines the range of the x axis to be from 1 to 7 
    y_axis, //Defines the range of the y axis to be from 1 to 5 
    maze, // This gives the external maze structure
    internal_walls, //This is the internal wall of the maze
    entrance_square, //Entry square(1,1)
    exit_square //Exit Square (1,5)
    
PROPERTIES
    // x-axis range is 1-7
    x_axis <: NATURAL1 & x_axis = 1..7 & 
    // y-axis range 1-5
    y_axis <: NATURAL1 & y_axis = 1..5 &
    // relation between x-axis and the y-axis range in the maze
    maze : x_axis <-> y_axis & maze = x_axis * y_axis &
    // maze is created by the multiplication of x and y axis 
    
    // internal_walls is an element of the relation between the x-axis and y-axis range 
    internal_walls : x_axis <-> y_axis &
    // Defining the internal_walls
    //function internal_walls, is mapping the x co-ordinate to the y co-ordinate
    //This uses a maplet because relation is a set of maplets, and a maplet is used for data mapping and since this is mapping out the internal walls in the maze, this is an appropriate use for it
    internal_walls = {
        (2 |-> 1), (6 |-> 1), (4 |-> 2), (6 |-> 2), (1 |-> 3), (2 |-> 3), (3 |-> 3), (4 |-> 3), (4 |-> 4), (6 |-> 4), (7 |-> 4), (2 |-> 5)
    } &
    // Defining the entry & exit square 
    entrance_square = {(1 |-> 1)} &
    exit_square = {(1 |-> 5)}
    
END    

