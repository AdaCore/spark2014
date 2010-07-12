------------------------------------------------------------------------------
--                                                                          --
--                            SPARKIFY COMPONENTS                           --
--                                                                          --
--                       S P A R K I F Y . C O M M O N                      --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                     Copyright (C) 2009-2010, AdaCore                     --
--                                                                          --
-- Sparkify is  free  software;  you can redistribute it  and/or  modify it --
-- under terms of the  GNU General Public License as published  by the Free --
-- Software Foundation;  either version  2,  or  (at your option) any later --
-- version. Sparkify is distributed in the hope that it will be useful, but --
-- WITHOUT ANY WARRANTY; without even the implied warranty of  MERCHANTABI- --
-- LITY or  FITNESS  FOR A  PARTICULAR  PURPOSE. See the GNU General Public --
-- License  for more details. You  should  have  received a copy of the GNU --
-- General Public License  distributed with GNAT; see file COPYING. If not, --
-- write to the Free Software Foundation,  51 Franklin Street, Fifth Floor, --
-- Boston,                                                                  --
--                                                                          --
-- Sparkify is maintained by AdaCore (http://www.adacore.com)               --
--                                                                          --
------------------------------------------------------------------------------

with Ada.Strings.Wide_Fixed;           use Ada.Strings.Wide_Fixed;
with Ada.Strings;                      use Ada.Strings;

with GNAT.OS_Lib;

with Asis.Declarations;                use Asis.Declarations;
with Asis.Text;                        use Asis.Text;
with Asis.Elements;                    use Asis.Elements;
with Asis.Expressions;                 use Asis.Expressions;
with Asis.Extensions.Flat_Kinds;       use Asis.Extensions.Flat_Kinds;

with ASIS_UL.Common;
with ASIS_UL.Output;                   use ASIS_UL.Output;

with Sparkify.Basic;                   use Sparkify.Basic;
with Sparkify.Names;                   use Sparkify.Names;

package body Sparkify.Common is

   -----------------------------
   -- Declaration_Unique_Name --
   -----------------------------

   function Declaration_Unique_Name
     (Element : Asis.Declaration) return Wide_String
   is
      Names : constant Defining_Name_List := Asis.Declarations.Names (Element);
   begin
      pragma Assert (Names'Length = 1);
      return Defining_Name_Image (Names (Names'First));
   end Declaration_Unique_Name;

   ------------------------
   -- Skip_Package_Names --
   ------------------------

   function Skip_Package_Names
     (Element : Asis.Expression) return Asis.Expression is
   begin
      --  Skip package names in prefix position in a selected component
      case Expression_Kind (Element) is
         when A_Selected_Component =>
            declare
               Prefix_Expr : constant Asis.Expression := Prefix (Element);
               Select_Expr : constant Asis.Expression := Selector (Element);
            begin
               case Expression_Kind (Prefix_Expr) is
               when An_Identifier =>
                  if Is_Package_Name (Prefix_Expr) then
                     return Skip_Package_Names (Select_Expr);
                  else
                     return Element;
                  end if;
               when A_Selected_Component =>
                  pragma Assert (False);
                  return Element;
               when others =>
                  return Element;
               end case;
            end;
         when others =>
            return Element;
      end case;
   end Skip_Package_Names;

   ------------------
   -- Element_Name --
   ------------------

   function Element_Name (Element : Asis.Element) return Wide_String is
   begin
      return Trim (Element_Image (Element), Left);
   end Element_Name;

   ----------------------
   -- Get_Package_Name --
   ----------------------

   function Get_Package_Name (Element : Asis.Element) return Wide_String is
      pragma Assert (Is_Package_Name (Element));
      Decl      : constant Asis.Declaration :=
                    Corresponding_Name_Declaration (Element);
      Names     : constant Defining_Name_List :=
                    Asis.Declarations.Names (Decl);
      pragma Assert (Names'Length = 1);
   begin
      return Flat_Package_Name (Defining_Name_Image (Names (Names'First)));
   end Get_Package_Name;

   -------------------------------
   -- Is_Subprogram_Declaration --
   -------------------------------

   function Is_Subprogram_Declaration (Element : Asis.Element) return Boolean
   is
   begin
      return Element_Kind (Element) = A_Declaration and then
        (Declaration_Kind (Element) = A_Function_Declaration or else
         Declaration_Kind (Element) = A_Function_Body_Declaration or else
         Declaration_Kind (Element) = A_Function_Body_Stub or else
         Declaration_Kind (Element) = A_Procedure_Declaration or else
         Declaration_Kind (Element) = A_Procedure_Body_Declaration or else
         Declaration_Kind (Element) = A_Procedure_Body_Stub);
   end Is_Subprogram_Declaration;

   ------------------------
   -- Is_Subprogram_Name --
   ------------------------

   function Is_Subprogram_Name (Expr : Asis.Expression) return Boolean is
   begin
      if Asis.Extensions.Is_Uniquely_Defined (Expr) then
         declare
            Decl : constant Asis.Declaration :=
                     Corresponding_Name_Declaration (Expr);
         begin
            return Is_Subprogram_Declaration (Decl);
         end;
      else
         return False;
      end if;
   end Is_Subprogram_Name;

   ----------------------------
   -- Is_Package_Declaration --
   ----------------------------

   function Is_Package_Declaration (Element : Asis.Element) return Boolean is
   begin
      return Element_Kind (Element) = A_Declaration and then
        (Declaration_Kind (Element) = A_Package_Declaration or else
           Declaration_Kind (Element) = A_Package_Body_Declaration);
   end Is_Package_Declaration;

   ---------------------
   -- Is_Package_Name --
   ---------------------

   function Is_Package_Name (Expr : Asis.Expression) return Boolean is
   begin
      if Asis.Extensions.Is_Uniquely_Defined (Expr) then
         declare
            Decl : constant Asis.Declaration :=
                     Corresponding_Name_Declaration (Expr);
         begin
            return Is_Package_Declaration (Decl);
         end;
      else
         return False;
      end if;
   end Is_Package_Name;

   ------------------------------
   -- Is_Package_Level_Element --
   ------------------------------

   function Is_Package_Level_Element (Element : Asis.Element) return Boolean is
      Encl_Element : constant Asis.Element := Enclosing_Element (Element);
   begin
      return Flat_Element_Kind (Encl_Element) = A_Package_Body_Declaration
        or else Flat_Element_Kind (Encl_Element) = A_Package_Declaration;
   end Is_Package_Level_Element;

   -------------------------
   -- SLOC_Error_And_Exit --
   -------------------------

   procedure SLOC_Error_And_Exit
     (Message : String;
      SLOC    : String) is
   begin
      SLOC_Error (Message, SLOC);
      GNAT.OS_Lib.OS_Exit (1);
   end SLOC_Error_And_Exit;

   ---------------------------------------
   -- Non_Implemented_ASIS_2005_Feature --
   ---------------------------------------

   procedure Non_Implemented_ASIS_2005_Feature
     (Element :        Asis.Element;
      Control : in out Traverse_Control;
      State   : in out Source_Traversal_State)
   is
   begin
      raise ASIS_UL.Common.Fatal_Error;
   end Non_Implemented_ASIS_2005_Feature;

   -------------------
   -- Initial_State --
   -------------------

   function Initial_State return Source_Traversal_State is
      Initial_Phase : Phase;
   begin
      case Current_Pass is
         when Effects => Initial_Phase := Global_Effects;
         when Printing =>
            declare
               Unit_Decl : constant Asis.Declaration :=
                             Unit_Declaration (The_Unit);
            begin
               if Declaration_Kind (Unit_Decl) = A_Package_Declaration then
                  Initial_Phase := Printing_Spec;
               else
                  Initial_Phase := Printing_Body;
               end if;
            end;
      end case;

      return
        (Phase       => Initial_Phase,
         Prefix_Len  => 0,
         Prefix      => (others => ' '),
         Echo_Cursor => File_Cursor (Kind => Before_File));
   end Initial_State;

   ---------------
   -- No_Action --
   ---------------

   procedure No_Action
     (Element :        Asis.Element;
      Control : in out Traverse_Control;
      State   : in out Source_Traversal_State)
   is
   begin
      pragma Unreferenced (Element);
      pragma Unreferenced (Control);
      pragma Unreferenced (State);
      null;
   end No_Action;

end Sparkify.Common;
