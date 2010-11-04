------------------------------------------------------------------------------
--                                                                          --
--                           GNAT2SPARK COMPONENTS                          --
--                                                                          --
--                    G N A T 2 S P A R K - D R I V E R                     --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                       Copyright (C) 2010, AdaCore                        --
--                                                                          --

-- gnat2spark is  free  software;  you can redistribute it and/or modify it --
-- under terms of the  GNU General Public License as published  by the Free --
-- Software Foundation;  either version  2,  or  (at your option) any later --
-- version. gnat2spark is distributed in the hope that it will  be  useful, --
-- but WITHOUT ANY WARRANTY; without even the implied warranty of MERCHAN-  --
-- TABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU General Public --
-- License  for more details. You  should  have  received a copy of the GNU --
-- General Public License  distributed with GNAT; see file COPYING. If not, --
-- write to the Free Software Foundation,  51 Franklin Street, Fifth Floor, --
-- Boston,                                                                  --
--                                                                          --
-- gnat2spark is maintained by AdaCore (http://www.adacore.com)             --
--                                                                          --
------------------------------------------------------------------------------

with GNAT.IO; use GNAT.IO;
with Switch;  use Switch;
with Sprint;  use Sprint;
with Atree;   use Atree;
with Errout;  use Errout;
with Treepr;
with Sinfo;   use Sinfo;

package body Gnat2SPARK.Driver is

   --   This is the main driver for the Ada-to-SPARK Back_End

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

   -------------------
   -- GNAT_To_SPARK --
   -------------------

   procedure GNAT_To_SPARK (GNAT_Root : Node_Id) is

      type Mode is (Only_SPARK,     --  all non-SPARK features lead to errors
                    Towards_ALFA);  --  all non-ALFA features lead to errors,
                                    --  all ALFA features not in SPARK lead to
                                    --  warnings

      Cur_Mode : constant Mode := Towards_ALFA;

      -----------------------
      -- Local Subprograms --
      -----------------------

      procedure Error_Not_ALFA (Msg : String; N : Node_Id);
      --  Issue an error message saying that the feature described in Msg and
      --  related to node N is not in ALFA

      function Exclude_Features (N : Node_Id) return Traverse_Result;
      --  Generate a message for non-ALFA features:
      --  * an error for features not in ALFA
      --  * a warning for features not yet supported, albeit in ALFA

      procedure Error_Not_SPARK (Msg : String; N : Node_Id);
      pragma Unreferenced (Error_Not_SPARK);
      --  Issue a warning message saying that the feature described in Msg and
      --  related to node N is not yet in the supported subset of ALFA

      --------------------
      -- Error_Not_ALFA --
      --------------------

      procedure Error_Not_ALFA (Msg : String; N : Node_Id) is
      begin
         case Cur_Mode is
            when Only_SPARK =>
               Error_Msg_N (Msg & " not in SPARK", N);
            when Towards_ALFA =>
               Error_Msg_N (Msg & " not in ALFA", N);
         end case;
      end Error_Not_ALFA;

      ---------------------
      -- Error_Not_SPARK --
      ---------------------

      procedure Error_Not_SPARK (Msg : String; N : Node_Id) is
      begin
         case Cur_Mode is
            when Only_SPARK =>
               Error_Msg_N (Msg & " not in SPARK", N);
            when Towards_ALFA =>
               Error_Msg_N (Msg & " not yet supported in ALFA?", N);
         end case;
      end Error_Not_SPARK;

      ----------------------
      -- Exclude_Non_ALFA --
      ----------------------

      function Exclude_Features (N : Node_Id) return Traverse_Result is
      begin
         case Nkind (N) is
            when N_Unused_At_Start =>
               pragma Assert (False);
               return OK;

            when N_Raise_xxx_Error =>
               if True or else Comes_From_Source (N) then
                  Error_Not_ALFA ("raising exceptions", N);
                  return Skip;
               else
                  --  This is an exception raised by a check inserted by
                  --  the compiler:
                  --  * Constraint_Error leads to generating a VC
                  --  * Program_Error and Storage_Error are ignored
                  return OK;
               end if;

            when N_Raise_Statement =>
               Error_Not_ALFA ("raising exceptions", N);
               return Skip;

            when N_Representation_Clause
               | N_Empty
               | N_Pragma_Argument_Association
               | N_Error
               =>
               Error_Not_ALFA ("(not yet decided)", N);
               return Skip;

            when others =>
               return OK;
         end case;
      end Exclude_Features;

      procedure Traverse_ALFA is new Traverse_Proc (Exclude_Features);

   begin
      New_Line;
      Put_Line ("*** GNAT2SPARK STUB ***");
      Put_Line ("NOTHING IMPLEMENTED SO FAR; this stub dumps:");
      Put_Line (" * the syntax tree;");
      Put_Line (" * a source-view of the syntax tree.");
      New_Line;

      Treepr.Print_Node_Subtree (GNAT_Root);
      Sprint_Node (GNAT_Root);
      Traverse_ALFA (GNAT_Root);
   end GNAT_To_SPARK;

end Gnat2SPARK.Driver;
