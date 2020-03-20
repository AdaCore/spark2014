------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                         X T R E E _ T A B L E S                          --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                     Copyright (C) 2010-2020, AdaCore                     --
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

with GNAT.Case_Util;             use GNAT.Case_Util;
with Utils;                      use Utils;

package body Xtree_Tables is

   function List_Type_Name (Kind : String) return String;
   function Param_Name (Field_Name : String) return String;
   --  Helper functions for the corresponding homonyms

   -------------------
   -- Accessor_Name --
   -------------------

   function Accessor_Name
     (Kind : Why_Node_Kind;
      IK   : Id_Kind;
      FI   : Field_Info)
     return String is
   begin
      if FI.Field_Kind = Field_Variant then
         if IK = Derived then
            return "Get_" & Strip_Prefix (FI.Field_Name.all);
         else
            return Strip_Prefix (Mixed_Case_Name (Kind))
              & "_Get_"
              & Strip_Prefix (FI.Field_Name.all);
         end if;
      else
         return "Get_" & FI.Field_Name.all;
      end if;
   end Accessor_Name;

   -----------------
   -- Buider_Name --
   -----------------

   function Builder_Name
     (Prefix : String;
      IK     : Id_Kind := Regular)
     return String is
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
     return String is
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
     return String
   is
   begin
      if Context = In_Builder_Spec
        and then Is_List (FI)
      then
         return Arr_Type (Node_Kind (FI), IK);
      else
         return Type_Name (FI, IK);
      end if;
   end Builder_Param_Type;

   -------------------
   -- Default_Value --
   -------------------

   function Default_Value
     (Kind    : Why_Node_Kind;
      FI      : Field_Info;
      IK      : Id_Kind := Regular;
      Context : Builder_Context := In_Builder_Body)
     return String is
   begin
      if Is_List (FI)
        and then (IK = Unchecked or else Maybe_Null (FI))
      then
         if Context = In_Builder_Body then
            return "New_List";
         else
            return "(2 .. 1 => <>)";
         end if;

      elsif Is_Why_Id (FI)
        and then (IK = Unchecked or else Maybe_Null (FI))
      then
         return "Why_Empty";

      elsif Field_Kind (FI) = Field_Domain then
         if Get_Domain (Kind) = EW_Expr then
            return "";
         else
            return "E" & Class_Name (Get_Domain (Kind));
         end if;

      else
         return FI.Default.all;
      end if;
   end Default_Value;

   -----------------------
   -- Element_Type_Name --
   -----------------------

   function Element_Type_Name
     (FI   : Field_Info;
      Kind : Id_Kind)
     return String is
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

   function Field_Kind (FI : Field_Info) return Field_Kind_Type is
   begin
      return FI.Field_Kind;
   end Field_Kind;

   ----------------
   -- Field_Name --
   ----------------

   function Field_Name (FI : Field_Info) return String is
   begin
      return FI.Field_Name.all;
   end Field_Name;

   ----------------
   -- Get_Domain --
   ----------------

   function Get_Domain (Kind : Why_Node_Kind) return EW_ODomain is
   begin
      return Why_Tree_Info (Kind).Domain;
   end Get_Domain;

   function Get_Domain (Kind : Why_Node_Kind) return Class_Info is
      DK : constant EW_ODomain := Get_Domain (Kind);
      DN : constant String := Mixed_Case_Name (DK);
      CN : constant String :=
             "W" & DN (DN'First + 2 .. DN'Last);
   begin
      for CI of Classes loop
         if Class_Name (CI) = CN then
            return CI;
         end if;
      end loop;

      pragma Assert (False);
      return (null, null, null, null);
   end Get_Domain;

   -----------------------
   -- Has_Default_Value --
   -----------------------

   function Has_Default_Value
     (Kind    : Why_Node_Kind;
      FI      : Field_Info;
      IK      : Id_Kind := Regular;
      Context : Builder_Context := In_Builder_Body)
     return Boolean is
   begin
      return Default_Value (Kind, FI, IK, Context) /= "";
   end Has_Default_Value;

   ----------------------
   -- Has_Variant_Part --
   ----------------------

   function Has_Variant_Part (Kind : Why_Node_Kind) return Boolean is
   begin
      return not Why_Tree_Info (Kind).Fields.Is_Empty;
   end Has_Variant_Part;

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

   function Is_Why_Id (FI : Field_Info) return Boolean is
   begin
      return FI.Is_Why_Id;
   end Is_Why_Id;

   ------------------
   -- List_Op_Name --
   ------------------

   function List_Op_Name
     (List_Op : List_Op_Kind)
     return String is
      Literal_Name : String := List_Op_Kind'Image (List_Op);
   begin
      To_Mixed (Literal_Name);
      return Strip_Prefix (Literal_Name);
   end List_Op_Name;

   ------------------
   -- List_Op_Name --
   ------------------

   function List_Op_Name
     (Kind    : Why_Node_Kind;
      FI      : Field_Info;
      List_Op : List_Op_Kind)
     return String is
   begin
      return Strip_Prefix (Mixed_Case_Name (Kind))
        & "_" & List_Op_Name (List_Op)
        & "_To_"
        & Strip_Prefix (FI.Field_Name.all);
   end List_Op_Name;

   --------------------
   -- List_Type_Name --
   --------------------

   function List_Type_Name (Kind : Why_Node_Kind) return String is
   begin
      return List_Type_Name (Mixed_Case_Name (Kind));
   end List_Type_Name;

   function List_Type_Name (Kind : String) return String is
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
     return String is
   begin
      if FI.Field_Kind = Field_Variant then
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
      Field_Kind : Field_Kind_Type;
      Field_Name : String;
      Field_Type : String;
      Default    : String)
   is
      FI           : Field_Info :=
                       (Field_Name     => new String'(Field_Name),
                        Field_Type     => new String'(Field_Type),
                        Default        => new String'(Default),
                        Id_Type        => null,
                        Field_Kind     => Field_Kind,
                        Is_Why_Id      => False,
                        Is_List        => False,
                        Maybe_Null     => False);
      Multiplicity : constant String := Suffix (FI.Field_Type.all);
   begin
      if Multiplicity = "Id"
        or else Multiplicity = "OId"
        or else Multiplicity = "List"
        or else Multiplicity = "OList"
      then
         declare
            Node_Kind : constant String :=
                          Strip_Suffix (FI.Field_Type.all);
            Checking  : constant String := Suffix (Node_Kind);
         begin
            if Checking = "Opaque" then
               FI.Is_Why_Id := True;

               if Multiplicity = "List" or else Multiplicity = "OList" then
                  FI.Is_List := True;
               end if;

               if Multiplicity = "OId" or else Multiplicity = "OList" then
                  FI.Maybe_Null := True;
               end if;

               FI.Id_Type := new String'(Strip_Suffix (Node_Kind)
                                              & "_" & Multiplicity);
            else
               FI.Id_Type := new String'(FI.Field_Type.all);
            end if;
         end;
      else
         FI.Id_Type := new String'(FI.Field_Type.all);
      end if;

      NI.Fields.Append (FI);
      NI.Max_Field_Name_Length :=
        Natural'Max (NI.Max_Field_Name_Length,
                     FI.Field_Name'Length);
   end New_Field;

   ---------------
   -- Node_Kind --
   ---------------

   function Node_Kind (FI : Field_Info) return String is
      Type_With_Visibility_Info : constant String :=
                                    Strip_Suffix (FI.Field_Type.all);
      Visibility_Info           : constant String :=
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
   end Node_Kind;

   ----------------
   -- Param_Name --
   ----------------

   function Param_Name (Field_Name : String) return String is
   begin
      return Strip_Prefix (Field_Name);
   end Param_Name;

   function Param_Name (FI : Field_Info) return String is
   begin
      if FI.Field_Kind = Field_Variant then
         return Param_Name (FI.Field_Name.all);
      else
         return FI.Field_Name.all;
      end if;
   end Param_Name;

   ---------------------------
   -- Max_Field_Name_Length --
   ---------------------------

   function Max_Field_Name_Length (Kind : Why_Node_Kind) return Natural is
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
      Variant_Part : constant Why_Node_Info := Why_Tree_Info (Kind);
      CF_Length    : constant Natural :=
                       (if Common_Field_Included then
                           Common_Fields.Max_Field_Name_Length
                       else 0);
   begin
      if Variant_Part.Fields.Is_Empty then
         return CF_Length;
      else
         declare
            First_FI      : constant Field_Info :=
                              Variant_Part.Fields.First_Element;
            First_Field   : constant String :=
                              First_FI.Field_Name.all;
            First_Param   : constant String :=
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
     (Field_Name : String;
      Field_Type : String;
      Default    : String := "") is
   begin
      New_Field (Common_Fields, Field_Common, Field_Name, Field_Type, Default);
   end New_Common_Field;

   ----------------------
   -- New_Domain_Field --
   ----------------------

   procedure New_Domain_Field
     (Field_Name : String;
      Field_Type : String;
      Default    : String := "") is
   begin
      New_Field (Common_Fields, Field_Domain, Field_Name, Field_Type, Default);
   end New_Domain_Field;

   ---------------
   -- New_Field --
   ---------------

   procedure New_Field
     (Kind       : Why_Node_Kind;
      Field_Name : String;
      Field_Type : String;
      Default    : String := "")
   is
      Prefix : String := Integer'Image (Why_Node_Kind'Pos (Kind)) & "_";
   begin
      Prefix (1) := 'K';
      New_Field (Why_Tree_Info (Kind),
                 Field_Variant,
                 Prefix & Field_Name,
                 Field_Type,
                 Default);
   end New_Field;

   procedure New_Field
     (Kind         : Why_Node_Kind;
      Field_Name   : String;
      Field_Kind   : String;
      Multiplicity : Id_Multiplicity) is
   begin
      New_Field (Kind,
                 Field_Name,
                 Id_Subtype (Field_Kind, Opaque, Multiplicity),
                 (case Multiplicity is
                    when Id_Lone => "Why_Empty",
                    when Id_Set  => "New_List",
                    when others  => ""));
   end New_Field;

   -----------------------
   -- New_Special_Field --
   -----------------------

   procedure New_Special_Field
     (Field_Name : String;
      Field_Type : String;
      Default    : String := "") is
   begin
      New_Field (Common_Fields, Field_Special,
                 Field_Name, Field_Type, Default);
   end New_Special_Field;

   -----------------
   -- Set_Mutable --
   -----------------

   procedure Set_Mutable (Kind : Why_Node_Kind) is
   begin
      Why_Tree_Info (Kind).Is_Mutable := True;
   end Set_Mutable;

   ----------------
   -- Set_Domain --
   ----------------

   procedure Set_Domain (Kind : Why_Node_Kind; Domain : EW_ODomain) is
   begin
      Why_Tree_Info (Kind).Domain := Domain;
   end Set_Domain;

   -----------------------
   -- Traversal_Post_Op --
   -----------------------

   function Traversal_Post_Op (Kind : Why_Node_Kind) return String is
   begin
      return Strip_Prefix (Mixed_Case_Name (Kind)) & "_Post_Op";
   end Traversal_Post_Op;

   ----------------------
   -- Traversal_Pre_Op --
   ----------------------

   function Traversal_Pre_Op (Kind : Why_Node_Kind) return String is
   begin
      return Strip_Prefix (Mixed_Case_Name (Kind)) & "_Pre_Op";
   end Traversal_Pre_Op;

   ---------------
   -- Type_Name --
   ---------------

   function Type_Name (FI   : Field_Info; Kind : Id_Kind) return String is
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
