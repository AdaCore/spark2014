------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                         X T R E E _ T A B L E S                          --
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
-- gnat2why is maintained by AdaCore (http://www.adacore.com)               --
--                                                                          --
------------------------------------------------------------------------------

with Ada.Characters.Conversions; use Ada.Characters.Conversions;
with Ada.Containers;   use Ada.Containers;
with GNAT.Case_Util; use GNAT.Case_Util;

package body Xtree_Tables is

   function Id_Type_Name (Kind : Wide_String) return Wide_String;
   function List_Type_Name (Kind : Wide_String) return Wide_String;
   function Param_Name (Field_Name : Wide_String) return Wide_String;
   --  Helper functions for the corresponding homonyms

   function Strip_Prefix (Name : Wide_String) return Wide_String;
   --  Strip anything that precedes the first underscord in Name
   --  and return the result.

   function Strip_Suffix (Name : Wide_String) return Wide_String;
   --  Strip anything that follows the last underscord in Name
   --  and return the result.

   function Suffix (Name : Wide_String) return Wide_String;

   -------------------
   -- Accessor_Name --
   -------------------

   function Accessor_Name
     (Kind : Why_Node_Kind;
      FI   : Field_Info)
     return Wide_String is
   begin
      if FI.In_Variant then
         return Strip_Prefix (Mixed_Case_Name (Kind))
           & "_Get_"
           & Strip_Prefix (FI.Field_Name.all);
      else
         return "Get_" & FI.Field_Name.all;
      end if;
   end Accessor_Name;

   -----------------
   -- Buider_Name --
   -----------------

   function Builder_Name (Kind : Why_Node_Kind) return Wide_String is
   begin
      return "New_" & Strip_Prefix (Mixed_Case_Name (Kind));
   end Builder_Name;

   ----------------
   -- Field_Name --
   ----------------

   function Field_Name (FI : Field_Info) return Wide_String is
   begin
      return FI.Field_Name.all;
   end Field_Name;

   ----------------------
   -- Has_Variant_Part --
   ----------------------

   function Has_Variant_Part (Kind : Why_Node_Kind) return Boolean is
      use Node_Lists;
   begin
      return Why_Tree_Info (Kind).Fields.Length > 0;
   end Has_Variant_Part;

   ------------------
   -- Id_Type_Name --
   ------------------

   function Id_Type_Name (Kind : Why_Node_Kind) return Wide_String is
   begin
      return Id_Type_Name (Mixed_Case_Name (Kind));
   end Id_Type_Name;

   function Id_Type_Name (Kind : Wide_String) return Wide_String is
   begin
      return Kind & "_Id";
   end Id_Type_Name;

   function Id_Type_Name (FI : Field_Info) return Wide_String is
      Multiplicity : constant Wide_String := Suffix (FI.Field_Type.all);
   begin
      return FI.Id_Type.all;
   end Id_Type_Name;

   ----------------
   -- In_Variant --
   ----------------

   function In_Variant (FI : Field_Info) return Boolean is
   begin
      return FI.In_Variant;
   end In_Variant;

   -------------
   -- Is_List --
   -------------

   function Is_List (FI : Field_Info) return Boolean is
   begin
      return FI.Is_List;
   end Is_List;

   ---------------
   -- Is_Why_Id --
   ---------------

   function Is_Why_Id  (FI : Field_Info) return Boolean is
   begin
      return FI.Is_Why_Id;
   end Is_Why_Id;

   --------------------
   -- List_Type_Name --
   --------------------

   function List_Type_Name (Kind : Why_Node_Kind) return Wide_String is
   begin
      return List_Type_Name (Mixed_Case_Name (Kind));
   end List_Type_Name;

   function List_Type_Name (Kind : Wide_String) return Wide_String is
   begin
      return Kind & "_List";
   end List_Type_Name;

   ----------------
   -- Maybe_Null --
   ----------------

   function Maybe_Null (FI : Field_Info) return Boolean is
   begin
      return FI.Maybe_Null;
   end Maybe_Null;

   ---------------
   -- New_Field --
   ---------------

   procedure New_Field
     (NI         : in out Why_Node_Info;
      In_Variant : Boolean;
      Field_Name : Wide_String;
      Field_Type : Wide_String)
   is
      FI           : Field_Info :=
                       (Field_Name     => new Wide_String'(Field_Name),
                        Field_Type     => new Wide_String'(Field_Type),
                        Id_Type        => null,
                        In_Variant     => In_Variant,
                        Is_Why_Id      => False,
                        Is_List        => False,
                        Maybe_Null     => False);
      Multiplicity : constant Wide_String := Suffix (FI.Field_Type.all);
      SF           : constant Special_Field_Kind :=
                       To_Special_Field_Kind (Field_Name);
   begin
      if SF /= Special_Field_None then
         Special_Fields (SF) := FI;
         return;
      end if;

      if Multiplicity = "Id"
        or else Multiplicity = "OId"
        or else Multiplicity = "List"
        or else Multiplicity = "OList"
      then
         declare
            Node_Kind : constant Wide_String :=
                          Strip_Suffix (FI.Field_Type.all);
            Checking  : constant Wide_String := Suffix (Node_Kind);
         begin
            if Checking = "Opaque" then
               FI.Is_Why_Id := True;

               if Multiplicity = "List" or else Multiplicity = "OList" then
                  FI.Is_List := True;
               end if;

               if Multiplicity = "OId" or else Multiplicity = "OList" then
                  FI.Maybe_Null := True;
               end if;

               FI.Id_Type := new Wide_String'(Strip_Suffix (Node_Kind)
                                              & "_" &Multiplicity);
            else
               FI.Id_Type := new Wide_String'(FI.Field_Type.all);
            end if;
         end;
      else
         FI.Id_Type := new Wide_String'(FI.Field_Type.all);
      end if;

      NI.Fields.Append (FI);
      NI.Max_Field_Name_Length :=
        Natural'Max (NI.Max_Field_Name_Length,
                     FI.Field_Name'Length);
   end New_Field;

   ----------------
   -- Param_Name --
   ----------------

   function Param_Name (Field_Name : Wide_String) return Wide_String is
   begin
      return Strip_Prefix (Field_Name);
   end Param_Name;

   function Param_Name (FI : Field_Info) return Wide_String is
   begin
      if FI.In_Variant then
         return Param_Name (FI.Field_Name.all);
      else
         return FI.Field_Name.all;
      end if;
   end Param_Name;

   ---------------------------
   -- Max_Field_Name_Length --
   ---------------------------

   function Max_Field_Name_Length (Kind : Why_Node_Kind) return Natural is
      use Node_Lists;

      Variant_Part  : constant Why_Node_Info := Why_Tree_Info (Kind);
   begin
      return Natural'Max
        (Variant_Part.Max_Field_Name_Length,
         Common_Fields.Max_Field_Name_Length);
   end Max_Field_Name_Length;

   ----------------------
   -- Max_Param_Length --
   ----------------------

   function Max_Param_Length (Kind : Why_Node_Kind) return Natural is
      use Node_Lists;

      Variant_Part  : constant Why_Node_Info := Why_Tree_Info (Kind);
   begin
      if Length (Variant_Part.Fields) = 0 then
         return Common_Fields.Max_Field_Name_Length;
      else
         declare
            First_FI      : constant Field_Info :=
                              Variant_Part.Fields.First_Element;
            First_Field   : constant Wide_String :=
                              First_FI.Field_Name.all;
            First_Param   : constant Wide_String :=
                              Param_Name (First_Field);
            Prefix_Len    : constant Natural :=
                              First_Field'Length - First_Param'Length;
         begin
            return Natural'Max
              (Variant_Part.Max_Field_Name_Length - Prefix_Len,
               Common_Fields.Max_Field_Name_Length);
         end;
      end if;
   end Max_Param_Length;

   ---------------------
   -- Mixed_Case_Name --
   ---------------------

   function Mixed_Case_Name (Kind : Why_Node_Kind) return Wide_String is
      Name : String := Why_Node_Kind'Image (Kind);
   begin
      To_Mixed (Name);
      return To_Wide_String (Name);
   end Mixed_Case_Name;

   ------------------
   -- Strip_Prefix --
   ------------------

   function Strip_Prefix (Name : Wide_String) return Wide_String is
      Start : Integer := Name'First;
   begin
      for J in Name'Range loop
         if Name (J) = '_' then
            Start := J + 1;
            exit;
         end if;
      end loop;

      return Name (Start .. Name'Last);
   end Strip_Prefix;

   ------------------
   -- Strip_Suffix --
   ------------------

   function Strip_Suffix (Name : Wide_String) return Wide_String is
      Stop : Integer := Name'Last;
   begin
      for J in reverse Name'Range loop
         if Name (J) = '_' then
            Stop := J - 1;
            exit;
         end if;
      end loop;

      return Name (Name'First .. Stop);
   end Strip_Suffix;

   ------------
   -- Suffix --
   ------------

   function Suffix (Name : Wide_String) return Wide_String is
      Stop : Integer := Name'Last;
   begin
      for J in reverse Name'Range loop
         if Name (J) = '_' then
            Stop := J;
            exit;
         end if;
      end loop;

      return Name (Stop + 1 .. Name'Last);
   end Suffix;

   ---------------------------
   -- To_Special_Field_Kind --
   ---------------------------

   function To_Special_Field_Kind
     (Name : Wide_String)
     return Special_Field_Kind is
   begin
      return Special_Field_Kind'Wide_Value (Special_Field_Prefix & Name);
   exception
      when Constraint_Error =>
         return Special_Field_None;
   end To_Special_Field_Kind;

   ---------------
   -- To_String --
   ---------------

   function To_String (Kind : Special_Field_Kind) return Wide_String is
      Enum_Literal_Name : constant String :=
                            Special_Field_Kind'Image (Kind);
      Result            : String :=
                            Enum_Literal_Name (Special_Field_Prefix'Last + 1
                                               .. Enum_Literal_Name'Last);
   begin
      To_Mixed (Result);
      return To_Wide_String (Result);
   end To_String;

   -----------------------
   -- Traversal_Post_Op --
   -----------------------

   function Traversal_Post_Op (Kind : Why_Node_Kind) return Wide_String is
   begin
      return Strip_Prefix (Mixed_Case_Name (Kind)) & "_Post_Op";
   end Traversal_Post_Op;

   ----------------------
   -- Traversal_Pre_Op --
   ----------------------

   function Traversal_Pre_Op (Kind : Why_Node_Kind) return Wide_String is
   begin
      return Strip_Prefix (Mixed_Case_Name (Kind)) & "_Pre_Op";
   end Traversal_Pre_Op;

end Xtree_Tables;
