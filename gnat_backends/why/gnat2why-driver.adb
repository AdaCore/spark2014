------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                      G N A T 2 W H Y - D R I V E R                       --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                       Copyright (C) 2010, AdaCore                        --
--                                                                          --
-- gnat2why is  free  software;  you can redistribute it and/or modify it   --
-- under terms of the  GNU General Public License as published  by the Free --
-- Software Foundation;  either version  2,  or  (at your option) any later --
-- version. gnat2why is distributed in the hope that it will  be  useful,   --
-- but WITHOUT ANY WARRANTY; without even the implied warranty of MERCHAN-  --
-- TABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU General Public --
-- License  for more details. You  should  have  received a copy of the GNU --
-- General Public License  distributed with GNAT; see file COPYING. If not, --
-- write to the Free Software Foundation,  51 Franklin Street, Fifth Floor, --
-- Boston,                                                                  --
--                                                                          --
-- gnat2why is maintained by AdaCore (http://www.adacore.com)             --
--                                                                          --
------------------------------------------------------------------------------

with GNAT.IO; use GNAT.IO;
with Switch;  use Switch;
with Sprint;  use Sprint;
with Treepr;

with Types; use Types;
with Namet; use Namet;

with Why.Types;          use Why.Types;
with Why.Atree.Builders; use Why.Atree.Builders;
with Why.Atree.Sprint;   use Why.Atree.Sprint;
with Why.Atree.Tables;   use Why.Atree.Tables;

package body Gnat2Why.Driver is

   --   This is the main driver for the Ada-to-Why back-end

   ------------------------
   -- Is_Back_End_Switch --
   ------------------------

   function Is_Back_End_Switch (Switch : String) return Boolean is
      First : constant Positive := Switch'First + 1;
      Last  : Natural           := Switch'Last;
   begin
      if Last >= First
        and then Switch (Last) = ASCII.NUL
      then
         Last := Last - 1;
      end if;

      if not Is_Switch (Switch) then
         return False;
      end if;

      --  For now we just allow the -g and -O switches, even though they
      --  will have no effect.

      case Switch (First) is
         when 'g' | 'O' =>
            return True;

         when others =>
            return False;
      end case;
   end Is_Back_End_Switch;

   -----------------
   -- GNAT_To_Why --
   -----------------

   procedure GNAT_To_Why (GNAT_Root : Node_Id) is
   begin
      New_Line;
      Put_Line ("*** GNAT2WHY STUB ***");
      Put_Line ("NOTHING IMPLEMENTED SO FAR; this stub dumps:");
      Put_Line (" * the syntax tree;");
      Put_Line (" * a source-view of the syntax tree;");
      Put_Line (" * a dummy test of the Why generator.");
      New_Line;

      Treepr.Print_Node_Subtree (GNAT_Root);
      Sprint_Node (GNAT_Root);

      declare
         I, T : Why_Node_Id;
      begin
         Name_Len := 0;
         Add_Str_To_Name_Buffer ("standard__integer");
         I := New_Identifier (Empty,
                              Why_Empty,
                              Name_Find,
                              Why_Empty);
         T := New_Type (Empty,
                        Why_Empty,
                        Why_Empty,
                        New_List,
                        I);
         Sprint_Why_Node (T);
      end;
   end GNAT_To_Why;

end Gnat2Why.Driver;
