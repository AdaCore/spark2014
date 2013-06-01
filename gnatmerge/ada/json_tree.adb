------------------------------------------------------------------------------
--                                                                          --
--                            J S O N _ T R E E                             --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                        Copyright (C) 2012-2013, AdaCore                  --
--                                                                          --
-- gnatmerge is  free  software;  you can redistribute it and/or  modify it --
-- under terms of the  GNU General Public License as published  by the Free --
-- Software  Foundation;  either version 3,  or (at your option)  any later --
-- version.  gnatprove is distributed  in the hope that  it will be useful, --
-- but WITHOUT ANY WARRANTY; without even the implied warranty of  MERCHAN- --
-- TABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU General Public --
-- License for  more details.  You should have  received  a copy of the GNU --
-- General Public License  distributed with  gnatprove;  see file COPYING3. --
-- If not,  go to  http://www.gnu.org/licenses  for a complete  copy of the --
-- license.                                                                 --
--                                                                          --
-- gnatmerge is maintained by AdaCore (http://www.adacore.com)              --
--                                                                          --
------------------------------------------------------------------------------

with Ada.Characters.Conversions; use Ada.Characters.Conversions;
with Ada.Containers;             use Ada.Containers;
with Ada.Containers.Hashed_Maps;
with Ada.Strings;                use Ada.Strings;
with Ada.Strings.Fixed;          use Ada.Strings.Fixed;
with Asis.Elements;              use Asis.Elements;
with Asis.Declarations;          use Asis.Declarations;
with Asis.Text;                  use Asis.Text;
with Asis.Set_Get;               use Asis.Set_Get;
with Asis.Iterator;              use Asis.Iterator;
with Asis.Implementation;        use Asis.Implementation;
with Asis.Compilation_Units;
with Asis.Ada_Environments;      use Asis.Ada_Environments;
with GNAT.Strings;               use GNAT.Strings;

package body Json_Tree is

   My_Context : Context;

   function Sloc_Image
     (CU_S : String;
      L    : Line_Number_Positive;
      C    : Character_Position_Positive)
     return String;

   function Hash (Key : Declaration_Kinds) return Hash_Type;

   function Extensional_Equal (Left, Right : String_Access) return Boolean;

   package Asis_Maps is
     new Ada.Containers.Hashed_Maps (Key_Type        => Declaration_Kinds,
                                     Element_Type    => String_Access,
                                     Hash            => Hash,
                                     Equivalent_Keys => "=",
                                     "="             => Extensional_Equal);

   Asis_Map : Asis_Maps.Map;
   --  ?? This ought to be associated to a sloc reader object. Make it
   --  global to start with.

   ----------
   -- Hash --
   ----------

   function Hash (Key : Declaration_Kinds) return Hash_Type is
   begin
      return Hash_Type'Mod (Declaration_Kinds'Pos (Key));
   end Hash;

   -----------------------
   -- Extensional_Equal --
   -----------------------

   function Extensional_Equal (Left, Right : String_Access) return Boolean is
   begin
      if Left = null or else Right = null then
         return Left = Right;
      else
         return Left.all = Right.all;
      end if;
   end Extensional_Equal;

   ------------
   -- Insert --
   ------------

   procedure Insert (Kind : Declaration_Kinds; Kind_Name : String) is
   begin
      Asis_Map.Insert (Kind, new String'(Kind_Name));
      --  ??? Duplication of Kind in each entry; we should use
      --  the same string access for the same value.
   end Insert;

   -------------
   -- Iterate --
   -------------

   procedure Iterate
     (Process : not null access procedure
        (Kind : String;
         Name : String;
         Sloc : String;
         Low  : String;
         High : String))
   is
      procedure Process_Element (E : Element; Name : String; Kind : String);

      type Traversal_State is record
         Indent : Integer := 0;
      end record;

      procedure Pre_Operation
        (Element : Asis.Element;
         Control : in out Traverse_Control;
         State   : in out Traversal_State);

      procedure Post_Operation
        (Element : Asis.Element;
         Control : in out Traverse_Control;
         State   : in out Traversal_State);

      procedure Traverse_Source is new Traverse_Element
        (State_Information => Traversal_State);

      procedure Pre_Operation
        (Element : Asis.Element;
         Control : in out Traverse_Control;
         State   : in out Traversal_State)
      is
         use Asis_Maps;

         Kind     : constant Declaration_Kinds := Declaration_Kind (Element);
         Position : constant Cursor := Asis_Map.Find (Kind);
         pragma Unreferenced (State);
         pragma Unreferenced (Control);
      begin
         if Position /= No_Element then
            declare
               NN : constant Defining_Name_List :=
                 Asis.Declarations.Names (Element);
            begin
               for N of NN loop
                  Process_Element
                    (Element,
                     To_String (Asis.Declarations.Defining_Name_Image (N)),
                     Asis_Maps.Element (Position).all);
               end loop;
            end;
         end if;
      end Pre_Operation;

      procedure Post_Operation
        (Element : Asis.Element;
         Control : in out Traverse_Control;
         State   : in out Traversal_State)
      is
         pragma Unreferenced (Element);
         pragma Unreferenced (Control);
         pragma Unreferenced (State);
      begin
         null;
      end Post_Operation;

      ---------------------
      -- Process_Element --
      ---------------------

      procedure Process_Element (E : Element; Name : String; Kind : String) is
         CU      : constant Compilation_Unit :=
           Enclosing_Compilation_Unit (E);
         CU_S    : constant String :=
           Source_File (CU);
         SP      : constant Span :=
           Element_Span (E);
         CD      : constant Element :=
           Corresponding_Declaration (E);
         Id      : constant Element :=
           (if CD = Nil_Element then E else CD);
         Id_CU   : constant Compilation_Unit :=
           Enclosing_Compilation_Unit (Id);
         Id_CU_S : constant String :=
           Source_File (Id_CU);
         Id_S    : constant Span :=
           Element_Span (Id);
      begin
         Process (Kind,
                  Name,
                  Sloc_Image (Id_CU_S, Id_S.First_Line, Id_S.First_Column),
                  Sloc_Image (CU_S, SP.First_Line, SP.First_Column),
                  Sloc_Image (CU_S, SP.Last_Line, SP.Last_Column));
      end Process_Element;

      Control : Traverse_Control := Continue;
      State   : Traversal_State;
   begin
      declare
         Next_Unit : Compilation_Unit;
         All_Units : constant Compilation_Unit_List :=
           Asis.Compilation_Units.Compilation_Units (My_Context);
      begin
         for I in All_Units'Range loop
            Next_Unit := All_Units (I);

            if Asis."=" (Asis.Compilation_Units.Unit_Origin (Next_Unit),
                         An_Application_Unit) then
               Traverse_Source (Unit_Declaration (Next_Unit),
                                Control,
                                State);
            end if;
         end loop;
      end;
   end Iterate;

   ----------
   -- Open --
   ----------

   procedure Open (File_Name : String) is
   begin
      Implementation.Initialize ("-ws");
      Ada_Environments.Associate
        (My_Context, "My Asis Context", "-C1 " & To_Wide_String (File_Name));
      Ada_Environments.Open (My_Context);
   end Open;

   -----------
   -- Close --
   -----------

   procedure Close is
   begin
      Ada_Environments.Close (My_Context);
      Ada_Environments.Dissociate (My_Context);
      Implementation.Finalize;
   end Close;

   ----------------
   -- Sloc_Image --
   ----------------

   function Sloc_Image
     (CU_S : String;
      L    : Line_Number_Positive;
      C    : Character_Position_Positive)
     return String
   is
      L_String : constant String := Trim (L'Img, Both);
      C_String : constant String := Trim (C'Img, Both);
   begin
      return CU_S & ":" & L_String & ":" & C_String;
   end Sloc_Image;

end Json_Tree;
