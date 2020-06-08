------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                        C E _ I N T E R V A L _ S E T S                   --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                     Copyright (C) 2010-2020, AdaCore                     --
--                                                                          --
-- gnat2why is  free  software;  you can redistribute  it and/or  modify it --
-- under terms of the  GNU General Public License as published  by the Free --
-- Software  Foundation;  either version 3,  or (at your option)  any later --
-- version.  gnat2why is distributed  in the hope that  it will be  useful, --
-- but WITHOUT ANY WARRANTY; without even the implied warranty of  MERCHAN- --
-- TABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU General Public --
-- License for  more details.  You should have  received  a copy of the GNU --
-- General  Public License  distributed with  gnat2why;  see file COPYING3. --
-- If not,  go to  http://www.gnu.org/licenses  for a complete  copy of the --
-- license.                                                                 --
--                                                                          --
-- gnat2why is maintained by AdaCore (http://www.adacore.com)               --
--                                                                          --
------------------------------------------------------------------------------
with Ada.Containers.Ordered_Sets;

generic
   --  type restricting the global interval
   type N is range <>;
package Ce_Interval_Sets is

   --  This package defines Sets of disjoint intervals

   --  The idea is to be able to add intervals to this set while keeping the
   --  intervals disjoints. We actually need two operations: adding an interval
   --  to the set, and querying if a number is inside the interval set.

   type Interval is record
      L_Bound : N;
      R_Bound : N;
   end record
     with Dynamic_Predicate =>
       Interval.L_Bound <= Interval.R_Bound;

   function "<" (X, Y : Interval) return Boolean is
     (X.R_Bound < Y.L_Bound);
   --  The order defined is intentionally not total for interval in general:
   --  overlapping intervals cannot be compared (X < Y or Y < X). So, we use
   --  the structure of ordered set to easily know if a new interval overlaps
   --  with one inside the set.
   --  X < Y means X is disjoint with Y and X is before Y.

   function "=" (X, Y : Interval) return Boolean is
     (not (X < Y) and not (Y < X));
   --  Equivalent_terms should be equal for the Ordered_Set data structure.
   --  Note that "and" is more efficient than "and then" in this context.
   --  X = Y means X overlaps with Y.

   type Interval_Set is tagged private;

   function Merge_Interval (X, Y : Interval) return Interval is
     (L_Bound => N'Min (X.L_Bound, Y.L_Bound),
      R_Bound => N'Max (X.R_Bound, Y.R_Bound))
   with Pre => (X = Y);
   --  This function takes two overlapping interval (X = Y) and merges them.

   procedure Insert (L : in out Interval_Set; Y : Interval);
   --  Insert an interval into an interval_set potentially merging newly
   --  overlapping intervals.

   procedure Insert_Union (L : in out Interval_Set; Add : Interval_Set);
   --  Insert an interval_set into another using Insert

   function Has_Containing_Interval (L : Interval_Set; X : N) return Boolean;
   --  Returns True if X is inside one of the intervals of L

   function Create return Interval_Set;
   --  Create the empty interval set

   procedure Clear (Container : in out Interval_Set);
   --  Reset the interval set to the empty interval

   Empty_Set : constant Interval_Set;

private

   --  We want to disallow calling directly functions on this data structure
   --  because they could possibly break the Interval_Set. For example, by
   --  adding two overlapping intervals to the set.
   package Intervals is new
     Ada.Containers.Ordered_Sets (Element_Type => Interval,
                                  "="          => "=",
                                  "<"          => "<");

   type Interval_Set is new Intervals.Set with null record;

   Empty_Set : constant Interval_Set := (Intervals.Empty_Set with null record);

end Ce_Interval_Sets;
