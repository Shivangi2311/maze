/* Maze_Robot
 * Author: Shivangi Shah
 * Creation date: 18-Dec-22
 */
MACHINE
    Maze_Robot
    
SETS
    REPORT = {Maze_Boundary, Maze_Internal_Wall, Moved_North, Moved_East, Moved_South, Moved_West, Cannot_Teleport_To_The_Same_Square,Teleported,Sqaure_visited_already, successful, failed,Exit_Square_Found}
    
CONSTANTS
    x_axis, //Defines the range of the x axis to be from 1 to 7 
    y_axis, //Defines the range of the y axis to be from 1 to 5 
    maze, // This gives the external maze structure
    internal_walls, //This is the internal wall of the maze
    entrance_square, //Entry square(1,1)
    exit_square //Exit Square (1,5)
    
VARIABLES
    x_Position, //robot's x position 
    y_Position,// robot's y position
    currentPosition,
    sqauresVisited    
    

INVARIANT
    // Robot's x-axis position in the maze in the range of 1-7
    x_Position : x_axis & 
    // Robot's y-axis position in the maze in the range of 1-5
    y_Position : y_axis & 
    // Shows the position the robot is right now 
    currentPosition : (NAT1 * NAT1) &
    // This keeps track of all the squares the robot visited
    // It uses a sequence so that is can store all the squares visited 
    sqauresVisited : seq(maze)
    
INITIALISATION
    // Initial positions of the robot (the entry square position),since the robot will always start from there 
    x_Position := 1 ||
    y_Position := 1 ||
    currentPosition := ( 1 |-> 1 ) ||
    sqauresVisited := [( 1 |-> 1 )]    
    
    
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

    
OPERATIONS
    
    report <-- MoveNorth = 
        PRE report : REPORT
        THEN
            //Stops the movement of the robot if the exit square is found
            IF (x_Position = 1 & y_Position = 5)
            THEN 
                report := Exit_Square_Found
            // Checks if the square the robot will move to (1 square up), is within the maze boundaries 
            ELSIF (y_Position + 1 > max(y_axis))
            THEN 
                report := Maze_Boundary
            // Checks if the square the robot will move to (1 square up), if it is an internal boundary or not
            ELSIF ((x_Position |-> y_Position + 1) : internal_walls) 
            THEN 
                report := Maze_Internal_Wall
                //If both the previous conditions are negative then it will move 1 square up and the new position will be added in visitedSquares (its path)
            ELSE 
                currentPosition := (x_Position |-> y_Position + 1) ||
                //this inserts the new square visited at the end of the sequence 
                sqauresVisited := (sqauresVisited <- (x_Position |-> y_Position + 1))||
                y_Position := y_Position + 1 ||
                report := Moved_North
            END
        END;
        
    report <-- MoveSouth = 
        PRE report : REPORT
        THEN
            //Stops the movement of the robot if the exit square is found
            IF (x_Position = 1 & y_Position = 5)
            THEN 
                report := Exit_Square_Found
            // Checks if the square the robot will move to (1 square below), is within the maze boundaries 
            ELSIF (y_Position - 1 < min(y_axis))
            THEN 
                report := Maze_Boundary
            // Checks if the square the robot will move to (1 square below), if it is an internal wall or not
            ELSIF ((x_Position |-> y_Position - 1) : internal_walls) 
            THEN 
                report := Maze_Internal_Wall
                //If both the previous conditions are negative then it will move 1 square below and the new position will be added in sqauresVisited (its path)
            ELSE 
                currentPosition := (x_Position |-> y_Position - 1) ||
                sqauresVisited := (sqauresVisited <- (x_Position |-> y_Position - 1))||
                y_Position := y_Position - 1 ||
                report := Moved_South
            END        
        END;


    report <-- MoveEast = 
        PRE report : REPORT
        THEN
            //Stops the movement of the robot if the exit square is found
            IF (x_Position = 1 & y_Position = 5)
            THEN 
                report := Exit_Square_Found
            // Checks if the square the robot will move to (1 square right), is within the maze boundaries 
            ELSIF (x_Position + 1 > max(x_axis))
            THEN 
                report := Maze_Boundary
            // Checks if the square the robot will move to (1 square right), if it is an internal wall or not 
            ELSIF ((x_Position + 1 |-> y_Position) : internal_walls) 
            THEN 
                report := Maze_Internal_Wall
                //If both the previous conditions are negative then it will move 1 square to the right and the new position will be added in sqauresVisited (its path)
            ELSE 
                currentPosition := (x_Position + 1 |-> y_Position) ||
                sqauresVisited := (sqauresVisited <- (x_Position + 1 |-> y_Position))||
                x_Position := x_Position + 1 ||
                report := Moved_East
            END
        END;


        report <-- MoveWest = 
            PRE report : REPORT
            THEN
                //Stops the movement of the robot if the exit square is found
                IF (x_Position = 1 & y_Position = 5)
                THEN 
                    report := Exit_Square_Found
                // Checks if the square the robot will move to (1 square left), is within the maze boundaries 
                ELSIF (x_Position - 1 < min(x_axis))
                THEN 
                    report := Maze_Boundary
                // Checks if the square the robot will move to (1 square left), if it is an internal wall or not 
                ELSIF ((x_Position - 1 |-> y_Position) : internal_walls) 
                THEN 
                    report := Maze_Internal_Wall
                    //If both the previous conditions are negative then it will move 1 square to the left and the new position will be added in sqauresVisited (its path)
                ELSE 
                    currentPosition := (x_Position - 1 |-> y_Position) ||
                    sqauresVisited := (sqauresVisited <- (x_Position - 1 |-> y_Position)) ||
                    x_Position := x_Position - 1 ||
                    report := Moved_West
                END
            END;


        report <-- Teleport(newXPosition, newYPosition) =
            PRE report : REPORT & 
                newXPosition : NAT1 & 
                newYPosition : NAT1
            THEN
                //Stops the movement of the robot if the exit square is found
                IF (x_Position = 1 & y_Position = 5)
                THEN 
                    report := Exit_Square_Found         
                // Makes sure that the robot doesn't teleport to an internal wall
                ELSIF ((newXPosition |-> newYPosition) : internal_walls)
                THEN 
                    report := Maze_Internal_Wall
                // Makes sure that the robot doesn't teleport to the same current square
                ELSIF (newXPosition = x_Position & newYPosition = y_Position)
                THEN
                    report := Cannot_Teleport_To_The_Same_Square
                // Makes sure that the robot doesn't teleport itself out of the maze
                ELSIF ((newXPosition |-> newYPosition) /: maze)
                THEN
                    report := Maze_Boundary
                ELSE
                    currentPosition := (newXPosition |-> newYPosition) ||
                    sqauresVisited := (sqauresVisited <- (newXPosition |-> newYPosition)) ||
                    x_Position := newXPosition ||
                    y_Position := newYPosition ||
                    report := Teleported
                END
            END;


        position <-- getPosition =
            BEGIN 
            position := currentPosition
            END;


        report <-- foundExit = 
            PRE report : REPORT
            THEN
                // Checks if the robot's current position is the exit square
                IF (currentPosition : exit_square)
                THEN 
                    report := successful
                ELSE 
                    report := failed
                END
            END;


      visitedSquare <-- hasVisitedSquare(Position_x_Visited, Position_y_Visited) =
          PRE visitedSquare : REPORT & Position_x_Visited : NAT1 & Position_y_Visited : NAT1
            THEN
                // Makes sure that the visited square x,y coordinates are within the maze
                IF ((Position_x_Visited |-> Position_y_Visited) : maze)
                THEN 
                    // Checks if the robot has already visited that square (Does not include the current square, but all the previous squares)
                    IF ((Position_x_Visited |-> Position_y_Visited) : ran(front(sqauresVisited)))
                    THEN 
                        visitedSquare := successful
                    ELSE
                        visitedSquare := failed
                    END
                ELSE
                    visitedSquare := Maze_Boundary
                END
            END;

        // route the robot took to reach the exit
        route <-- robotsRoute =
            BEGIN
                route := sqauresVisited
            END;
            
       // this resets the robot to the original position 
        reset = 
        BEGIN
            x_Position := 1 ||
            y_Position := 1 ||
            currentPosition := ( 1 |-> 1 ) ||
            sqauresVisited := [( 1 |-> 1 )]
        END    
END
