------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                      G N A T 2 W H Y - D R I V E R                       --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                       Copyright (C) 2010-2011, AdaCore                   --
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
-- gnat2why is maintained by AdaCore (http://www.adacore.com)               --
--                                                                          --
------------------------------------------------------------------------------

with Atree;                use Atree;
with Gnat2Why.Subprograms; use Gnat2Why.Subprograms;
with Gnat2Why.Types;       use Gnat2Why.Types;
with Nlists;               use Nlists;
with Opt;                  use Opt;
with Outputs;              use Outputs;
with Sinfo;                use Sinfo;
with Sprint;               use Sprint;
with Switch;               use Switch;
with Stand;                use Stand;
with Treepr;
with Why.Atree.Builders;   use Why.Atree.Builders;
with Why.Atree.Sprint;     use Why.Atree.Sprint;
with Why.Ids;              use Why.Ids;

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

   procedure Translate_List_Of_Decls (File : W_File_Id; Decls : List_Id);

   -----------------------------
   -- Translate_List_Of_Decls --
   -----------------------------

   procedure Translate_List_Of_Decls (File : W_File_Id; Decls : List_Id)
   is
      Decl  : Node_Id;
      function Is_Type_Node (N : Node_Id) return Boolean;
      --  Detect if a node of an Ada Tree is a typing declaration

      function Is_Func_Or_Proc_Node (N : Node_Id) return Boolean;
      --  Detect if a node is a function or procedure declaration

      ------------------
      -- Is_Type_Node --
      ------------------

      function Is_Type_Node (N : Node_Id) return Boolean is
      begin
         case Nkind (N) is
            when N_Full_Type_Declaration | N_Subtype_Declaration =>
               return True;
            when others => return False;
         end case;
      end Is_Type_Node;

      --------------------------
      -- Is_Func_Or_Proc_Node --
      --------------------------

      function Is_Func_Or_Proc_Node (N : Node_Id) return Boolean is
      begin
         case Nkind (N) is
            when N_Subprogram_Body =>
               return True;
            when others => return False;
         end case;
      end Is_Func_Or_Proc_Node;

   begin
      Decl := First (Decls);
      while Present (Decl) loop
         if Is_Type_Node (Decl) then
            Why_Type_Decl_of_Gnat_Type_Decl (File, Decl);
         end if;

         if Is_Func_Or_Proc_Node (Decl) then
            --  ?? TODO
            null;
         end if;

         Next (Decl);
      end loop;
   end Translate_List_Of_Decls;

   -----------------
   -- GNAT_To_Why --
   -----------------

   procedure GNAT_To_Why (GNAT_Root : Node_Id)
   is
      File : constant W_File_Id := New_File;
   begin
      if Print_Generated_Code then
         Treepr.Print_Node_Subtree (GNAT_Root);
         Sprint_Node (GNAT_Root);
      end if;

      Translate_List_Of_Decls
        (File,
         Visible_Declarations (Specification (Standard_Package_Node)));

      if Nkind (GNAT_Root) = N_Compilation_Unit then
         if Nkind (Unit (GNAT_Root)) = N_Subprogram_Body then
            Why_Decl_of_Ada_Subprogram (File, Unit (GNAT_Root));
         else
            case Nkind (Unit (GNAT_Root)) is
               when N_Package_Body =>
                  Translate_List_Of_Decls
                    (File,
                     Declarations (Unit (GNAT_Root)));
               when N_Package_Declaration =>
                  Translate_List_Of_Decls
                    (File,
                     Visible_Declarations (Specification (Unit (GNAT_Root))));
               when others => raise Program_Error;
            end case;
         end if;
         --  ??? TBD: create a file that has a meaningful name, depending on
         --  the input file
         Open_Current_File ("out.why");
         Sprint_Why_Node (File, Current_File);
         Close_Current_File;
      end if;
   end GNAT_To_Why;

end Gnat2Why.Driver;
