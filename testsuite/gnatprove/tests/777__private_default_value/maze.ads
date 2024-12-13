--
--            Copyright (C) 2008-2010, AdaCore
--

package Maze with SPARK_Mode is

   type Puzzle (<>) is limited private;
   --  This type represents mazes to be solved and is a singleton. All
   --  references to the one actual object are acquired via function Instance.

   type Reference is access Puzzle;

   type Reference_Constant is access constant Puzzle;

   function Instance return Reference_Constant;
   --  Returns a pointer to the single instance that is maintained by
   --  this package.

   type Position is private;
   --  Represents individual locations on a maze.

   function Make_Position (Row, Column : Natural) return Position;

   function Row    (This : Position) return Natural;
   function Column (This : Position) return Natural;

   type Moves is range 0 .. 4;
   --  There are at most four possible subsequent positions from any position
   --  in a maze, including the previous position *behind* the current
   --  location, because we do not traverse diagonally. However, in some cases
   --  there are no further positions to visit (i.e., dead ends and the exit).
   --  When counting moves, we need to include that possibility so the lower
   --  bound is zero.

   subtype Possible_Moves is Moves range 1 .. Moves'Last;
   --  A one-based subtype used as an index for the array type Positions

   type Positions is array (Possible_Moves range <>) of Position;
   --  The array type Positions represents the physically possible moves from a
   --  given position. It is unconstrained since the number of possible moves
   --  from any position depends on the specific maze traversed.

   function On_Grid (This : not null access constant Puzzle;  Proposed : Position)
      return Boolean;
   --  Returns whether the Proposed position in within This.Grid

   function Next (This : not null access constant Puzzle; Current : Position) return Positions
      with Pre => On_Grid (This, Current);
   --  Returns all the physically possible moves from the current position. The
   --  result will be a null (i.e., empty) array if no further moves are
   --  possible. The predecessor to the current position is included.
   --  Physically possible moves are those next to the Current position that
   --  do not have a wall in between.

   function Entrance (This : not null access constant Puzzle) return Position;
   function The_Exit (This : not null access constant Puzzle) return Position;

   function At_Exit (This : not null access constant Puzzle; Here : Position) return Boolean;

   function Rows (This : not null access constant Puzzle) return Natural;
   --  Returns the number of physical rows in This. These maze puzzles are of
   --  sizes specified by the user, hence they are not hard-coded.

   function Columns (This : not null access constant Puzzle) return Natural ;
   --  Returns the number of physical columns in This.

   function North_Wall_Present (This : not null access constant Puzzle;  Here : Position)
      return Boolean
   with
      Pre => On_Grid (This, Here);


   function South_Wall_Present (This : not null access constant Puzzle;  Here : Position)
      return Boolean
   with
      Pre => On_Grid (This, Here);

   function East_Wall_Present  (This : not null access constant Puzzle;  Here : Position)
      return Boolean
   with
      Pre => On_Grid (This, Here);

   function West_Wall_Present  (This : not null access constant Puzzle;  Here : Position)
      return Boolean
   with
      Pre => On_Grid (This, Here);

private

   type Position is
      record
         Row    : Natural;
         Column : Natural;
      end record;

   type Wall_Names is (North, South, East, West);

   type Wall_Flags is array (Wall_Names) of Boolean;

   type Cell is
      record
         Walls : Wall_Flags := [others => True];
         --  we may add fields later, eg for displaying backtracking etc, so we
         --  use a record type instead of simply making the maze rep be an
         --  array of wall_flags
      end record;

   type Maze_Representation is
      array (Positive range <>, Positive range <>) of Cell;

   type Layout is access Maze_Representation;

   subtype Actual_Index is Natural range 1 .. Natural'Last-1;

   type Puzzle is
      record
         Start_Point    : Position;
         End_Point      : Position;
         Actual_Rows    : Actual_Index := 1;
         Actual_Columns : Actual_Index := 1;
         Grid           : Layout;
      end record
   with
      Predicate =>
         Grid /= null and then

         Grid'First (1) = 1 and then
         Grid'Last  (1) = Actual_Rows and then

         Grid'First (2) = 1 and then
         Grid'Last  (2) = Actual_Columns;

   --  The following are internal utility declarations, made visible here for
   --  the sake of child packages in case any ever exist.

   type Offset is
      record
         Row    : Integer range -1 .. 1;
         Column : Integer range -1 .. 1;
      end record;
   --  The type Offset allows the program to explore adjacent cells in a maze,
   --  relative to some current position.

   Offsets : constant array (Wall_Names) of Offset :=
               [North => (-1, 0),
                South => (+1, 0),
                East  => (0, +1),
                West  => (0, -1)];
   --  The constant Offsets provides a means of defining the adjacent cells in
   --  a maze.

   function "+" (Left : Position; Right : Offset) return Position is
      (Position'(Left.Row + Right.Row, Left.Column + Right.Column))
   with
      Pre =>
         Right.Row    <= Natural'Last - Left.Row and then
         Right.Column <= Natural'Last - Left.Column and then

         Left.Row    >= -Right.Row and then
         Left.Column >= -Right.Column;
   --  Returns the position resulting from the addition of the corresponding
   --  rows and columns. The result will potentially be an adjacent cell in a
   --  maze, but may not be in those cases where Left is on the perimeter. Such
   --  cases are handled elsewhere (see function On_Grid below).

   function On_Grid (This : not null access constant Puzzle;  Proposed : Position)
      return Boolean
   is
      (Proposed.Row    in 1 .. This.Actual_Rows and
       Proposed.Column in 1 .. This.Actual_Columns);
   --  Returns whether the Proposed position in within This.Grid

   function Adjacent_Cells
      (Proposed, Current : Position) return Boolean
   is
      (Proposed.Row    = Current.Row or else
       Proposed.Column = Current.Column);

   function Acceptable
     (This : not null access constant Puzzle;  Proposed, Current : Position) return Boolean
   with
      Pre =>
         On_Grid (This, Current) and then
         Adjacent_Cells (Proposed, Current);
   --  Returns whether Proposed is on This.Grid and there is no wall between
   --  Proposed and Current.

   function No_Wall_Between
     (This : not null access constant Puzzle;  Proposed, Current : Position) return Boolean
   with
      Pre =>
         On_Grid (This, Proposed) and then
         On_Grid (This, Current) and then
         Adjacent_Cells (Proposed, Current);

   --  Returns whether there is a wall between Proposed and Current.

   procedure Delete_Wall_Between
     (This : not null access Puzzle;  Cell1, Cell2 : Position)
   with
      Pre =>
         On_Grid (This, Cell1) and then
         On_Grid (This, Cell2) and then
         Adjacent_Cells (Cell1, Cell2),
      Post =>
         This.Actual_Rows    = This.Actual_Rows'Old and
         This.Actual_Columns = This.Actual_Columns'Old and
         This.Start_Point    = This.Start_Point'Old and
         This.End_Point      = This.End_Point'Old and

         On_Grid (This, Cell1) and
         On_Grid (This, Cell2) and
         Adjacent_Cells (Cell1, Cell2);
   --  Deletes the wall between the two positions.

   The_Instance : Reference;
   --  This is the singleton pointer shared by all reference requests.

end Maze;
