------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                      G N A T 2 W H Y - T Y P E S                         --
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

with Atree;              use Atree;
with Einfo;              use Einfo;
with Nlists;             use Nlists;
with Sem_Eval;           use Sem_Eval;
with Sinfo;              use Sinfo;
with String_Utils;       use String_Utils;
with Uintp;              use Uintp;
with Why;                use Why;
with Why.Atree.Builders; use Why.Atree.Builders;
with Why.Gen.Arrays;     use Why.Gen.Arrays;
with Why.Gen.Ints;       use Why.Gen.Ints;
with Why.Gen.Enums;      use Why.Gen.Enums;

package body Gnat2Why.Types is

   -------------------------
   -- Type_Of_Array_Index --
   -------------------------

   function Type_Of_Array_Index (N : Node_Id) return Name_Id
   is
   begin
      return Chars (Etype (First (Discrete_Subtype_Definitions (N))));
   end Type_Of_Array_Index;

   -------------------------------------
   -- Why_Type_Decl_of_Full_Type_Decl --
   -------------------------------------

   procedure Why_Type_Decl_of_Full_Type_Decl
      (File       : W_File_Id;
       Ident_Node : Node_Id;
       Def_Node   : Node_Id)
   is
      Name     : constant Name_Id := Chars (Ident_Node);
      Name_Str : constant String := Get_Name_String (Name);
   begin
      case Nkind (Def_Node) is
         when N_Enumeration_Type_Definition =>
            declare
               Cursor       : Node_Or_Entity_Id :=
                                Nlists.First (Literals (Def_Node));
               Constructors : String_Lists.List :=
                                String_Lists.Empty_List;
            begin
               while Nkind (Cursor) /= N_Empty loop
                  Constructors.Append (
                    Get_Name_String (Chars (Cursor)));
                  Cursor := Next (Cursor);
               end loop;
               Declare_Ada_Enum_Type (File, Name_Str, Constructors);
            end;

         when N_Signed_Integer_Type_Definition =>
            Declare_Ada_Abstract_Signed_Int
              (File,
               Name_Str,
               Expr_Value (Low_Bound (Def_Node)),
               Expr_Value (High_Bound (Def_Node)));
         when N_Floating_Point_Definition
            | N_Ordinary_Fixed_Point_Definition
            | N_Unconstrained_Array_Definition
            | N_Record_Definition
            =>
            --  ??? We do nothing here for now
            null;
         when N_Constrained_Array_Definition =>
            declare
               Component_Type : constant String :=
                  Get_Name_String
                    (Chars (Subtype_Indication
                       (Component_Definition (Def_Node))));
               Index          : constant String :=
                  Get_Name_String (Type_Of_Array_Index (Def_Node));
            begin
               Declare_Ada_Constrained_Array
                  (File,
                   Name_Str,
                   Index,
                   Component_Type);
            end;

         when N_Derived_Type_Definition =>
            --  ??? Is this correct?
            Why_Type_Decl_of_Subtype_Decl
               (File,
                Ident_Node,
                Subtype_Indication (Def_Node));

         when others =>
            raise Not_Implemented;
      end case;
   end Why_Type_Decl_of_Full_Type_Decl;

   -----------------------------------
   -- Why_Type_Decl_of_Subtype_Decl --
   -----------------------------------

   procedure Why_Type_Decl_of_Subtype_Decl
      (File       : W_File_Id;
       Ident_Node : Node_Id;
       Sub_Ind    : Node_Id)
   is
      Name     : constant Name_Id := Chars (Ident_Node);
      Name_Str : constant String := Get_Name_String (Name);
   begin
      case Nkind (Sub_Ind) is
         when N_Identifier =>
            declare
               Sc_Range   : constant Node_Id :=
                  Scalar_Range (Ident_Node);
               Low       : constant Uint :=
                  Expr_Value (Low_Bound (Sc_Range));
               High       : constant Uint :=
                  Expr_Value (High_Bound (Sc_Range));

            begin
               Declare_Ada_Abstract_Signed_Int
                 (File,
                  Name_Str,
                  Low,
                  High);
            end;
         when N_Subtype_Indication =>
            case Nkind (Constraint (Sub_Ind)) is
            when N_Range_Constraint =>
               declare
                  Sc_Range  : constant Node_Id :=
                     Range_Expression (Constraint (Sub_Ind));
                  Low       : constant Uint :=
                     Expr_Value (Low_Bound (Sc_Range));
                  High      : constant Uint :=
                     Expr_Value (High_Bound (Sc_Range));
               begin
                  Declare_Ada_Abstract_Signed_Int
                    (File,
                     Name_Str,
                     Low,
                     High);
               end;
            when N_Index_Or_Discriminant_Constraint =>
               --  ??? In at least one case (generated code for
               --  'Image of enums) we should not treat this case
               null;
            when others =>
               raise Not_Implemented;
            end case;
         when N_Range =>
            declare
               Low  : constant Uint :=
                  Expr_Value (Low_Bound (Sub_Ind));
               High : constant Uint :=
                  Expr_Value (High_Bound (Sub_Ind));
            begin
               Declare_Ada_Abstract_Signed_Int (File, Name_Str, Low, High);
            end;

         when others  =>
            raise Unexpected_Node;
      end case;
   end Why_Type_Decl_of_Subtype_Decl;

   -------------------------------
   -- Why_Prog_Type_of_Ada_Type --
   -------------------------------

   function Why_Prog_Type_of_Ada_Type
     (Ty : Node_Id) return W_Simple_Value_Type_Id
   is
      Name      : constant Name_Id := Chars (Etype (Ty));
      Base_Type : W_Primitive_Type_Id;

   begin
      Base_Type :=
        (if Is_Boolean_Type (Entity (Ty)) then
           New_Type_Bool
         else
           New_Abstract_Type
             (Ada_Node => Ty,
              Name     => New_Identifier
                (Ada_Node => Ty,
                 Symbol   => Name)));
      return
        New_Ref_Type
          (Ada_Node     => Ty,
           Aliased_Type => Base_Type);
   end  Why_Prog_Type_of_Ada_Type;

end Gnat2Why.Types;
