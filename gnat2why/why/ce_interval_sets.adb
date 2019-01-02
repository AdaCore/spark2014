------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                        C E _ I N T E R V A L _ S E T S                   --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                     Copyright (C) 2010-2019, AdaCore                     --
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

package body Ce_Interval_Sets is

   ------------
   -- Insert --
   ------------

   procedure Insert (L : in out Interval_Set; Y : Interval) is
      Position : Intervals.Cursor;
      Inserted : Boolean;
      X        : Interval := Y;
   begin
      --  This terminates because L'length decreases
      loop
         L.Insert (X, Position, Inserted);

         if Inserted then
            --  Case where X did not overlap with anything
            return;
         else
            --  Case where X overlap with something (equivalent in the sense of
            --  Sets) we now try to insert the merge of these two values.
            X := Merge_Interval (L (Position), X);

            L.Delete (Position);

         end if;
      end loop;
   end Insert;

   ------------------
   -- Insert_Union --
   ------------------

   procedure Insert_Union (L : in out Interval_Set; Add : Interval_Set) is
   begin
      for Elt of Add loop
         Insert (L, Elt);
      end loop;
   end Insert_Union;

   -----------------------------
   -- Has_Containing_Interval --
   -----------------------------

   function Has_Containing_Interval (L : Interval_Set;
                                     X : N)
                                     return Boolean
   --  Test if an interval in the set is "=" to [X; X] (in the term of
   --  equivalent_terms which means overlapping).
   is
     (L.Contains (Interval'(L_Bound => X, R_Bound => X)));

   -----------
   -- Clear --
   -----------

   procedure Clear (Container : in out Interval_Set) is
   begin
      Intervals.Clear (Intervals.Set (Container));
   end Clear;

   ------------
   -- Create --
   ------------

   function Create return Interval_Set is
   begin
      return (Intervals.Empty_Set with null record);
   end Create;

end Ce_Interval_Sets;
