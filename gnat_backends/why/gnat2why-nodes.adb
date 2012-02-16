------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                       G N A T 2 W H Y . N O D E S                        --
--                                                                          --
--                                  B o d y                                 --
--                                                                          --
--                        Copyright (C) 2012, AdaCore                       --
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

with Lib;       use Lib;

package body Gnat2Why.Nodes is

   function Is_Main_Cunit (N : Node_Id) return Boolean is
     (Get_Cunit_Unit_Number (Parent (N)) = Main_Unit);

   function Is_Spec_Unit_Of_Main_Unit (N : Node_Id) return Boolean is
     (Present (Corresponding_Body (N))
       and then Is_Main_Cunit
        (Unit (Enclosing_Lib_Unit_Node (Corresponding_Body (N)))));

   package body Ada_Ent_To_Why is

      -------------
      -- Element --
      -------------

      function Element (M : Map; E : Entity_Id)
                            return Why_Node_Id is
      begin
         return M.Entity_Ids.Element (E);
      end Element;

      function Element (C : Cursor) return Why_Node_Id is
      begin
         case C.Kind is
            when CK_Ent =>
               return Ada_To_Why.Element (C.Ent_Cursor);
            when CK_Str =>
               return Name_To_Why_Map.Element (C.Name_Cursor);
         end case;
      end Element;

      ----------
      -- Find --
      ----------

      function Find (M : Map; E : Entity_Id)
                     return Cursor is
         C : constant Ada_To_Why.Cursor := M.Entity_Ids.Find (E);
      begin
         if Ada_To_Why.Has_Element (C) then
            return Cursor'(CK_Ent,
                           M.Entity_Ids.Find (E),
                           Name_To_Why_Map.No_Element);

            --  We need to check the name map, but before generating a string
            --  to look up, let's check if the map is empty

         elsif Name_To_Why_Map.Is_Empty (M.Entity_Names) then

               --  The dummy cursor

               return Cursor'(CK_Ent, Ada_To_Why.No_Element,
                              Name_To_Why_Map.No_Element);
         else
            declare
               S   : Entity_Name := new String'(Unique_Name (E));
               Res : constant Cursor := Cursor'(CK_Str, Ada_To_Why.No_Element,
                                                M.Entity_Names.Find (S));
            begin
               Free (S);
               return Res;
            end;
         end if;
      end Find;

      -----------------
      -- Has_Element --
      -----------------

      function Has_Element (M : Map; E : Entity_Id) return Boolean
      is
      begin
         return M.Entity_Ids.Contains (E);
      end Has_Element;

      function Has_Element (C : Cursor) return Boolean
      is
      begin
         case C.Kind is
            when CK_Ent =>
               return Ada_To_Why.Has_Element (C.Ent_Cursor);
            when CK_Str =>
               return Name_To_Why_Map.Has_Element (C.Name_Cursor);
         end case;
      end Has_Element;

      ------------
      -- Insert --
      ------------

      procedure Insert (M : in out Map;
                        E : Entity_Id;
                        W : Why_Node_Id) is
      begin
         M.Entity_Ids.Insert (E, W);
      end Insert;

      procedure Insert (M : in out Map;
                        E : String;
                        W : Why_Node_Id) is
      begin
         M.Entity_Names.Insert (new String'(E), W);
      end Insert;

   end Ada_Ent_To_Why;

   -----------------------
   -- In_Main_Unit_Body --
   -----------------------

   function In_Main_Unit_Body (N : Node_Id) return Boolean is
      CU   : constant Node_Id := Enclosing_Lib_Unit_Node (N);
      Root : Node_Id;

   begin
      if No (CU) then
         return False;
      end if;

      Root := Unit (CU);

      case Nkind (Root) is
         when N_Package_Body    |
              N_Subprogram_Body =>

            return Is_Main_Cunit (Root);

         --  The only way a node in a subunit can be seen is when this subunit
         --  is part of the main unit.

         when N_Subunit =>
            return True;

         when N_Package_Declaration            |
              N_Generic_Package_Declaration    |
              N_Subprogram_Declaration         |
              N_Generic_Subprogram_Declaration =>

            return False;

         when N_Package_Renaming_Declaration           |
              N_Generic_Package_Renaming_Declaration   |
              N_Subprogram_Renaming_Declaration        |
              N_Generic_Function_Renaming_Declaration  |
              N_Generic_Procedure_Renaming_Declaration =>

            return False;

         when others =>
            raise Program_Error;
      end case;
   end In_Main_Unit_Body;

   -----------------------
   -- In_Main_Unit_Spec --
   -----------------------

   function In_Main_Unit_Spec (N : Node_Id) return Boolean is
      CU   : constant Node_Id := Enclosing_Lib_Unit_Node (N);
      Root : Node_Id;

   begin
      if No (CU) then
         return False;
      end if;

      Root := Unit (CU);

      case Nkind (Root) is
         when N_Package_Body    |
              N_Subprogram_Body |
              N_Subunit         =>

            return False;

         when N_Package_Declaration            |
              N_Generic_Package_Declaration    |
              N_Subprogram_Declaration         |
              N_Generic_Subprogram_Declaration =>

            return Is_Main_Cunit (Root)
              or else Is_Spec_Unit_Of_Main_Unit (Root);

         when N_Package_Renaming_Declaration           |
              N_Generic_Package_Renaming_Declaration   |
              N_Subprogram_Renaming_Declaration        |
              N_Generic_Function_Renaming_Declaration  |
              N_Generic_Procedure_Renaming_Declaration =>

            return False;

         when others =>
            raise Program_Error;
      end case;
   end In_Main_Unit_Spec;

   ------------------------
   -- Is_In_Current_Unit --
   ------------------------

   function Is_In_Current_Unit (N : Node_Id) return Boolean is
      Real_Node : constant Node_Id :=
        (if Is_Itype (N) then Associated_Node_For_Itype (N) else N);
   begin

      --  ??? Should be made more efficient

      return In_Main_Unit_Spec (Real_Node) or else
        In_Main_Unit_Body (Real_Node);
   end Is_In_Current_Unit;

   ------------------------------
   -- Safe_Instantiation_Depth --
   ------------------------------

   function Safe_Instantiation_Depth (Id : Unique_Entity_Id) return Int
   is
      S : constant Source_Ptr := Sloc (+Id);
   begin
      if S /= Standard_ASCII_Location then
         return Instantiation_Depth (S);
      else
         return 0;
      end if;
   end Safe_Instantiation_Depth;

end Gnat2Why.Nodes;
