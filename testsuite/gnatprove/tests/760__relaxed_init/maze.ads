--
--            Copyright (C) 2008-2010, AdaCore
--

package Maze with SPARK_Mode is

   type Puzzle (<>) is limited private;
   --  This type represents mazes to be solved and is a singleton. All
   --  references to the one actual object are acquired via function Instance.

   type Reference is access all Puzzle;

   --  type Any_Maze is access all Puzzle'Class;

   type Position is private;
   --  Represents individual locations on a maze.

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
         Walls : Wall_Flags := (others => True);
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



   procedure Generate
     (Width   : in Positive;
      Height  : in Positive;
      Perfect : in Boolean := True)
   with
      Pre =>
         Width  < Positive'Last - 1 and then
         Height < Positive'Last - 1 and then
         Height < Positive'Last / Width;
end Maze;
