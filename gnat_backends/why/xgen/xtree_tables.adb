------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                         X T R E E _ T A B L E S                          --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                       Copyright (C) 2010-2011, AdaCore                   --
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

with Ada.Characters.Conversions; use Ada.Characters.Conversions;
with Ada.Containers;             use Ada.Containers;
with GNAT.Case_Util;             use GNAT.Case_Util;
with Utils;                      use Utils;

package body Xtree_Tables is

   function List_Type_Name (Kind : Wide_String) return Wide_String;
   function Param_Name (Field_Name : Wide_String) return Wide_String;
   --  Helper functions for the corresponding homonyms

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

   function Builder_Name
     (Prefix : Wide_String;
      IK     : Id_Kind := Regular)
     return Wide_String is
   begin
      if IK = Unchecked then
         return "New_Unchecked_" & Strip_Prefix (Prefix);
      else
         return "New_" & Strip_Prefix (Prefix);
      end if;
   end Builder_Name;

   ------------------
   -- Builder_Name --
   ------------------

   function Builder_Name
     (Kind : Why_Node_Kind;
      IK   : Id_Kind := Regular)
     return Wide_String is
   begin
      return Builder_Name (Mixed_Case_Name (Kind), IK);
   end Builder_Name;

   ------------------------
   -- Builder_Param_Type --
   ------------------------

   function Builder_Param_Type
     (FI      : Field_Info;
      IK      : Id_Kind;
      Context : Builder_Context)
     return Wide_String
   is
   begin
      if Context = In_Builder_Spec
        and then Is_List (FI)
      then
         return Arr_Type (Field_Kind (FI), IK);
      else
         return Type_Name (FI, IK);
      end if;
   end Builder_Param_Type;

   -------------------
   -- Default_Value --
   -------------------

   function Default_Value
     (FI      : Field_Info;
      IK      : Id_Kind := Regular;
      Context : Builder_Context := In_Builder_Body)
     return Wide_String is
      TN : constant Wide_String := Type_Name (FI, Regular);
   begin
      if TN = "Why_Node_Id" then
         return "Why_Empty";
      elsif TN = "Node_Id" then
         return "Empty";
      elsif TN = "Why_Node_Set" then
         return "Why_Empty";
      elsif Is_List (FI)
        and then (IK = Unchecked or else Maybe_Null (FI))
      then
         if Context = In_Builder_Body then
            return "New_List";
         else
            return "(2 .. 1 => <>)";
         end if;
      elsif Is_Why_Id (FI)
        and then (IK = Unchecked or else Maybe_Null (FI)) then
         return "Why_Empty";
      else
         return "";
      end if;
   end Default_Value;

   -----------------------
   -- Element_Type_Name --
   -----------------------

   function Element_Type_Name
     (FI   : Field_Info;
      Kind : Id_Kind)
     return Wide_String is
   begin
      case Kind is
         when Opaque =>
            return Strip_Suffix (FI.Id_Type.all) & "_Opaque_Id";
         when Unchecked =>
            return Strip_Suffix (FI.Id_Type.all) & "_Unchecked_Id";
         when Regular =>
            return Strip_Suffix (FI.Id_Type.all) & "_Valid_Id";
         when Derived =>
            return Strip_Suffix (FI.Id_Type.all) & "_Id";
      end case;
   end Element_Type_Name;

   ----------------
   -- Field_Kind --
   ----------------

   function Field_Kind (FI : Field_Info) return Wide_String is
      Type_With_Visibility_Info : constant Wide_String :=
                                    Strip_Suffix (FI.Field_Type.all);
      Visibility_Info           : constant Wide_String :=
                                    Suffix (Type_With_Visibility_Info);
   begin
      if Visibility_Info = "Opaque"
        or else Visibility_Info = "Unchecked"
        or else Visibility_Info = "Valid"
      then
         return Strip_Suffix (Type_With_Visibility_Info);
      else
         return Type_With_Visibility_Info;
      end if;
   end Field_Kind;

   ----------------
   -- Field_Name --
   ----------------

   function Field_Name (FI : Field_Info) return Wide_String is
   begin
      return FI.Field_Name.all;
   end Field_Name;

   -----------------------
   -- Has_Default_Value --
   -----------------------

   function Has_Default_Value
     (FI      : Field_Info;
      IK      : Id_Kind := Regular;
      Context : Builder_Context := In_Builder_Body)
     return Boolean is
   begin
      return Default_Value (FI, IK, Context) /= "";
   end Has_Default_Value;

   ----------------------
   -- Has_Variant_Part --
   ----------------------

   function Has_Variant_Part (Kind : Why_Node_Kind) return Boolean is
      use Node_Lists;
   begin
      return Why_Tree_Info (Kind).Fields.Length > 0;
   end Has_Variant_Part;

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

   ----------------
   -- Is_Mutable --
   ----------------

   function Is_Mutable (Kind : Why_Node_Kind) return Boolean is
   begin
      return Why_Tree_Info (Kind).Is_Mutable;
   end Is_Mutable;

   ---------------
   -- Is_Why_Id --
   ---------------

   function Is_Why_Id  (FI : Field_Info) return Boolean is
   begin
      return FI.Is_Why_Id;
   end Is_Why_Id;

   ------------------
   -- List_Op_Name --
   ------------------

   function List_Op_Name
     (List_Op : List_Op_Kind)
     return Wide_String is
      Literal_Name : String := List_Op_Kind'Image (List_Op);
   begin
      To_Mixed (Literal_Name);
      return Strip_Prefix (To_Wide_String (Literal_Name));
   end List_Op_Name;

   ------------------
   -- List_Op_Name --
   ------------------

   function List_Op_Name
     (Kind    : Why_Node_Kind;
      FI      : Field_Info;
      List_Op : List_Op_Kind)
     return Wide_String is
   begin
      return Strip_Prefix (Mixed_Case_Name (Kind))
        & "_" & List_Op_Name (List_Op)
        & "_To_"
        & Strip_Prefix (FI.Field_Name.all);
   end List_Op_Name;

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

   ------------------
   -- Multiplicity --
   ------------------

   function Multiplicity (FI : Field_Info) return Id_Multiplicity is
   begin
      if FI.Maybe_Null then
         if FI.Is_List then
            return Id_Set;
         else
            return Id_Lone;
         end if;
      else
         if FI.Is_List then
            return Id_Some;
         else
            return Id_One;
         end if;
      end if;
   end Multiplicity;

   ------------------
   -- Mutator_Name --
   ------------------

   function Mutator_Name
     (Kind : Why_Node_Kind;
      FI   : Field_Info)
     return Wide_String is
   begin
      if FI.In_Variant then
         return Strip_Prefix (Mixed_Case_Name (Kind))
           & "_Set_"
           & Strip_Prefix (FI.Field_Name.all);
      else
         return "Set_" & FI.Field_Name.all;
      end if;
   end Mutator_Name;

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
                                              & "_" & Multiplicity);
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

   function Max_Param_Length
     (Kind                  : Why_Node_Kind;
      Common_Field_Included : Boolean := True)
     return Natural
   is
      use Node_Lists;

      Variant_Part : constant Why_Node_Info := Why_Tree_Info (Kind);
      CF_Length    : constant Natural :=
                       (if Common_Field_Included then
                           Common_Fields.Max_Field_Name_Length
                       else 0);
   begin
      if Length (Variant_Part.Fields) = 0 then
         return CF_Length;
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
               CF_Length);
         end;
      end if;
   end Max_Param_Length;

   ----------------------
   -- New_Common_Field --
   ----------------------

   procedure New_Common_Field
     (Field_Name : Wide_String;
      Field_Type : Wide_String) is
   begin
      New_Field (Common_Fields, False, Field_Name, Field_Type);
   end New_Common_Field;

   ---------------
   -- New_Field --
   ---------------

   procedure New_Field
     (Kind       : Why_Node_Kind;
      Field_Name : Wide_String;
      Field_Type : Wide_String)
   is
      Prefix : Wide_String :=
                 Integer'Wide_Image (Why_Node_Kind'Pos (Kind)) & "_";
   begin
      Prefix (1) := 'K';
      New_Field (Why_Tree_Info (Kind), True, Prefix & Field_Name, Field_Type);
   end New_Field;

   procedure New_Field
     (Kind         : Why_Node_Kind;
      Field_Name   : Wide_String;
      Field_Kind   : Wide_String;
      Multiplicity : Id_Multiplicity) is
   begin
      New_Field (Kind, Field_Name,
                 Id_Subtype (Field_Kind, Opaque, Multiplicity));
   end New_Field;

   -----------------------------
   -- Register_Special_Fields --
   -----------------------------

   procedure Register_Special_Fields is
   begin
      for Kind in Valid_Special_Field_Kind'Range loop
         New_Field (Common_Fields,
                    False,
                    To_String (Kind),
                    Special_Field_Type (Kind));
      end loop;
   end Register_Special_Fields;

   -----------------
   -- Set_Mutable --
   -----------------

   procedure Set_Mutable (Kind : Why_Node_Kind) is
   begin
      Why_Tree_Info (Kind).Is_Mutable := True;
   end Set_Mutable;

   ------------------------
   -- Special_Field_Type --
   ------------------------

   function Special_Field_Type
     (Kind : Valid_Special_Field_Kind) return Wide_String is
   begin
      case Kind is
         when Special_Field_Link =>
            return "Why_Node_Set";

         when Special_Field_Checked =>
            return "Boolean";
      end case;
   end Special_Field_Type;

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

   ---------------
   -- Type_Name --
   ---------------

   function Type_Name (FI   : Field_Info; Kind : Id_Kind) return Wide_String is
   begin
      if Is_Why_Id (FI) then
         return Id_Subtype (Strip_Suffix (FI.Id_Type.all),
                            Kind,
                            Multiplicity (FI));
      else
         return FI.Field_Type.all;
      end if;
   end Type_Name;

end Xtree_Tables;
