------------------------------------------------------------------------------
--                                                                          --
--                           GNAT2WHY COMPONENTS                            --
--                                                                          --
--                 F L O W . G E N E R A T E D _ G L O B A L S              --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                Copyright (C) 2017-2021, Altran UK Limited                --
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
------------------------------------------------------------------------------

with Ada.Text_IO;
with GNATCOLL.Utils;
with SPARK_Util;     use SPARK_Util;

package body Flow_Generated_Globals is

   Debug_Tree_Traversal : constant Boolean := True and XXX;
   --  Display entity names as the entity tree is traversed

   ---------------------
   -- Debug_Traversal --
   ---------------------

   procedure Debug_Traversal (E : Entity_Id) is
   begin
      if Debug_Tree_Traversal then
         Term_Info.Set_Style (Dim);
         Ada.Text_IO.Put_Line
           ("Finished " &
              Full_Source_Name (E) &
              " (" & GNATCOLL.Utils.Image (Integer (E), 1) & ")" &
              " with contracts:");
         Term_Info.Set_Style (Normal);
      end if;
   end Debug_Traversal;

   --------------
   -- Disjoint --
   --------------

   function Disjoint (A, B, C : Name_Sets.Set) return Boolean is
   begin
      return not
        (for some E of A => B.Contains (E) or else C.Contains (E))
          or else
        (for some E of B => C.Contains (E));
   end Disjoint;

--  Start of processing for Flow_Generated_Globals

begin
   Term_Info.Init_For_Stdout (Colors => Yes);
end Flow_Generated_Globals;
