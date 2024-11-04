--
--            Copyright (C) 2008-2010, AdaCore
--

with Unbounded_Sequential_Stacks;
package body Maze with SPARK_Mode is

   subtype Possible_Neighbors is Integer range 1 .. 4;
   --  we can only go north, south, east, or west, ie not diagonally,
   --  so a cell can have at most 4 neighbors

   type Neighbor_List is array (Possible_Neighbors range <>) of Position;

   package Positions_Pack is new Unbounded_Sequential_Stacks (Position);
   use Positions_Pack;


   --------------
   -- Generate --
   --------------

   procedure Generate
      (Width   : Positive;
       Height  : Positive;
       Perfect : Boolean := True)
   is

      Visited_Positions : Positions_Pack.Stack;
      X : Integer := Width * 10;
   begin
     null;

   end Generate;

   ----------------------
   -- Intact_Neighbors --
   ----------------------

   function Intact_Neighbors (This : Position; The_Maze : Reference)
      return Neighbor_List
   is
      Result : Neighbor_List (Possible_Neighbors) with Relaxed_Initialization;
      Count  : Integer range 0 .. Possible_Neighbors'Last := 0;
   begin
     return Result;
   end Intact_Neighbors;

   All_Walls_Present : constant Wall_Flags := (others => True);
   --  A constant indicating that all four walls are present
end Maze;
