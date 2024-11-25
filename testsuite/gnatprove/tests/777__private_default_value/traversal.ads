--
--            Copyright (C) 2008-2013, AdaCore
--

with Maze;
with SPARK.Containers.Formal.Doubly_Linked_Lists;

-- with Bounded_Dynamic_Arrays;

package Traversal with SPARK_Mode is

   type Trail is private;
   --  A Trail represents a single solution path within a maze.

   Origin : constant Trail;

   procedure Copy (Source : in Trail; To : out Trail);
   --  More efficient that the assignment operation because it only copies the
   --  parts that are currently assigned.

   procedure Mark (Point  :        Maze.Position;
                   Past   : in out Trail;
                   Within :        access constant Maze.Puzzle;
                   Next   :    out Maze.Positions;
                   Last   :    out Maze.Moves);
   --  Adds position Point to the solution trail Past.
   --  Returns in Next all the positions that can be visited from that Point on
   --  the maze Within, if any, and indicates the Last index of Next that was
   --  assigned a value. Last might be zero, as when a dead-end is encountered
   --  at Point or Point is the exit. Next will not include the position we
   --  just came from, thereby preventing solution path circularities.

private

   --  type Positions_List is array (Positive range <>) of Maze.Position;

   --  package Positions is new Bounded_Dynamic_Arrays
   --    (Component  => Maze.Position,
   --     List_Index => Positive,
   --     List       => Positions_List);
   --  An object of type Positions.Sequence is a bounded, logically varying
   --  length array of Maze.Position values. It is a wrapper for Positions_List
   --  arrays.

   package Positions is new SPARK.Containers.Formal.Doubly_Linked_Lists
     (Element_Type => Maze.Position,
      "=" => Maze."=");

   Intersections_Capacity : constant := 500; -- arbitrary
   Solutions_Capacity     : constant := 1000; -- arbitrary

   type Trail is
      record
         Intersections : Positions.List (Intersections_Capacity);
         Solutions     : Positions.List (Solutions_Capacity);
      end record;
   --  A trail is actually a tuple consisting of a list of solution positions
   --  paired with a list of intersections included in that solution. All the
   --  positions in a given maze solution are included in the Solutions list.
   --  Intersections are positions from which more than one subsequent position
   --  can be visited, i.e., intersections are forks in a path. All positions
   --  in Intersections are also in Solutions.
   --
   --  The list of intersections is used to detect and prevent circular
   --  solution paths. When determining if a given position has already been
   --  visited, instead of examining every position in the solution we can just
   --  examine the intersections because positions between intersections are
   --  not of interest. Essentially it is an optimized representation of all
   --  the positions visited by the Solutions list.
   --
   --  The chosen capacity values are arbitrary but do put a limit on the
   --  mazes that can be solved. These sequences are saved and restored (i.e.,
   --  copied) if a searcher thread is not available when a fork in the path is
   --  encountered, and they are per-thread objects, so size is a consideration.

   Origin : constant Trail := (others => <>);

   function Previously_Visited (This : Maze.Position; Past : Trail)
      return Boolean;
   --  Prevents circularities by answering "Have we been there before?"

   function Is_Member (This : Maze.Position;  Within : Positions.List) return Boolean;
   --  Returns whether This maze position occurs within the list of positions
   --  designated by Within.

   procedure Plot (This : Trail);
   --  Displays a given solution trail on the selected console.  This is not a
   --  thread-safe routine and is therefore not called directly by threads.

end Traversal;
