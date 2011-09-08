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

with Atree;              use Atree;
with Einfo;              use Einfo;
with Gnat2Why.Decls;     use Gnat2Why.Decls;
with Namet;              use Namet;
with Sem_Eval;           use Sem_Eval;
with Sem_Util;           use Sem_Util;
with Sinfo;              use Sinfo;
with Stand;              use Stand;
with String_Utils;       use String_Utils;
with Why;                use Why;
with Why.Sinfo;          use Why.Sinfo;
with Why.Conversions;    use Why.Conversions;
with Why.Atree.Builders; use Why.Atree.Builders;
with Why.Gen.Arrays;     use Why.Gen.Arrays;
with Why.Gen.Decl;       use Why.Gen.Decl;
with Why.Gen.Enums;      use Why.Gen.Enums;
with Why.Gen.Scalars;    use Why.Gen.Scalars;
with Why.Gen.Names;      use Why.Gen.Names;
with Why.Gen.Records;    use Why.Gen.Records;
with Why.Gen.Binders;    use Why.Gen.Binders;
with Why.Inter;          use Why.Inter;

with Gnat2Why.Expr;      use Gnat2Why.Expr;

package body Gnat2Why.Types is

   procedure Declare_Ada_Abstract_Signed_Int_From_Range
     (File : W_File_Id;
      Name : String;
      Rng  : Node_Id);
   --  Same as Declare_Ada_Abstract_Signed_Int but extract range information
   --  from node.

   procedure Declare_Ada_Floating_Point_From_Range
     (File : W_File_Id;
      Name : String;
      Rng  : Node_Id);
   --  Same as Declare_Ada_Floating_Point but extract range information
   --  from node.

   ------------------------------------------------
   -- Declare_Ada_Abstract_Signed_Int_From_Range --
   ------------------------------------------------

   procedure Declare_Ada_Abstract_Signed_Int_From_Range
     (File : W_File_Id;
      Name : String;
      Rng  : Node_Id)
   is
      Range_Node : constant Node_Id := Get_Range (Rng);
   begin
      Declare_Ada_Abstract_Signed_Int
        (File,
         Name,
         Expr_Value (Low_Bound (Range_Node)),
         Expr_Value (High_Bound (Range_Node)));
   end Declare_Ada_Abstract_Signed_Int_From_Range;

   ------------------------------------------------
   -- Declare_Ada_Floating_Point_From_Range --
   ------------------------------------------------

   procedure Declare_Ada_Floating_Point_From_Range
     (File : W_File_Id;
      Name : String;
      Rng  : Node_Id)
   is
      Range_Node : constant Node_Id := Get_Range (Rng);
   begin
      Declare_Ada_Floating_Point
        (File,
         Name,
         Expr_Value_R (Low_Bound (Range_Node)),
         Expr_Value_R (High_Bound (Range_Node)));
   end Declare_Ada_Floating_Point_From_Range;

   -------------------------------
   -- Why_Logic_Type_Of_Ada_Obj --
   -------------------------------

   function Why_Logic_Type_Of_Ada_Obj
     (N : Node_Id)
     return W_Primitive_Type_Id
   is
      Ty : constant Entity_Id := Unique_Entity (Etype (N));
   begin
      return New_Abstract_Type (Ty, EW_Term, New_Identifier (Full_Name (Ty)));
   end  Why_Logic_Type_Of_Ada_Obj;

   --------------------------------
   -- Why_Logic_Type_Of_Ada_Type --
   --------------------------------

   function Why_Logic_Type_Of_Ada_Type
     (Ty : Node_Id)
     return W_Primitive_Type_Id
   is
      T : constant Entity_Id := Unique_Entity (Ty);
   begin
      return New_Abstract_Type (T, EW_Term, New_Identifier (Full_Name (T)));
   end  Why_Logic_Type_Of_Ada_Type;

   -----------------------------
   -- Why_Type_Decl_Of_Entity --
   -----------------------------

   procedure Why_Type_Decl_Of_Entity
      (File       : W_File_Id;
       Name_Str   : String;
       Ident_Node : Node_Id) is
   begin
      if Ident_Node = Standard_Boolean then
         null;

      elsif Ident_Node = Standard_Character or else
              Ident_Node = Standard_Wide_Character or else
              Ident_Node = Standard_Wide_Wide_Character then
         Declare_Ada_Abstract_Signed_Int_From_Range
           (File,
            Name_Str,
            Ident_Node);

      else
         case Ekind (Ident_Node) is
            when E_Enumeration_Type =>
               declare
                  Constructors : String_Lists.List := String_Lists.Empty_List;
                  Cur_Lit      : Entity_Id :=
                                   First_Literal (Ident_Node);
               begin
                  while Present (Cur_Lit) loop
                     Constructors.Append (Full_Name (Cur_Lit));
                     Next_Literal (Cur_Lit);
                  end loop;
                  Declare_Ada_Enum_Type (File, Name_Str, Constructors);
               end;

            when E_Signed_Integer_Type
               | E_Signed_Integer_Subtype
               | E_Enumeration_Subtype =>
               Declare_Ada_Abstract_Signed_Int_From_Range
                 (File,
                  Name_Str,
                  Scalar_Range (Ident_Node));

            when E_Floating_Point_Type | E_Floating_Point_Subtype =>
               Declare_Ada_Floating_Point_From_Range
                 (File,
                  Name_Str,
                  Scalar_Range (Ident_Node));

            when Array_Kind =>
               declare
                  Comp_Type : constant String :=
                                Full_Name (Component_Type (Ident_Node));
               begin
                  if Is_Constrained (Ident_Node) then
                     declare
                        Rng : constant Node_Id :=
                                Get_Range (First_Index (Ident_Node));
                     begin
                        Declare_Ada_Constrained_Array
                          (File,
                           Name_Str,
                           Comp_Type,
                           Expr_Value (Low_Bound (Rng)),
                           Expr_Value (High_Bound (Rng)));
                     end;

                  else
                     Declare_Ada_Unconstrained_Array
                       (File,
                        Name_Str,
                        Comp_Type);
                  end if;
               end;

            when E_Record_Type =>
               declare
                  Number_Of_Fields : Natural := 0;
                  Field            : Node_Id := First_Entity (Ident_Node);
               begin
                  while Present (Field) loop
                     if Ekind (Field) in Object_Kind then
                        Number_Of_Fields := Number_Of_Fields + 1;
                     end if;

                     Next_Entity (Field);
                  end loop;

                  declare
                     Field   : Node_Id := First_Entity (Ident_Node);
                     Binders : Binder_Array (1 .. Number_Of_Fields);
                     J       : Natural := 0;
                  begin
                     while Present (Field) loop
                        if Ekind (Field) in Object_Kind then
                           declare
                              C_Name : constant String :=
                                         Name_Str & "__" &
                                         Get_Name_String (Chars (Field));
                           begin
                              J := J + 1;
                              Binders (J) :=
                                (B_Name => New_Identifier (C_Name),
                                 B_Type =>
                                   Why_Logic_Type_Of_Ada_Type (Etype (Field)),
                                 others => <>);
                           end;
                        end if;

                        Next_Entity (Field);
                     end loop;
                     Define_Ada_Record (File, Name_Str, Binders);
                  end;
               end;

            when Private_Kind =>

               --  This can happen when we have a private type which is
               --  derived from a private type. We just generate an
               --  abstract type here.

               Emit (File, New_Type (Name_Str));

            when others =>
               raise Not_Implemented;
         end case;
      end if;

   end Why_Type_Decl_Of_Entity;

   procedure Why_Type_Decl_Of_Entity
      (File       : W_File_Id;
       Ident_Node : Node_Id)
   is
      Name_Str : constant String := Full_Name (Ident_Node);
   begin
      Why_Type_Decl_Of_Entity (File, Name_Str, Ident_Node);
   end Why_Type_Decl_Of_Entity;

   -------------------------------
   -- Why_Prog_Type_Of_Ada_Type --
   -------------------------------

   function Why_Prog_Type_Of_Ada_Type (Ty : Node_Id; Is_Mutable : Boolean)
      return W_Simple_Value_Type_Id
   is
      Name : constant String := Full_Name (Ty);
      Base : constant W_Primitive_Type_Id :=
               New_Abstract_Type (Ty, EW_Term, New_Identifier (Name));
   begin
      if Is_Mutable then
         return New_Ref_Type (Ada_Node => Ty, Aliased_Type => Base);
      else
         return +Base;
      end if;
   end  Why_Prog_Type_Of_Ada_Type;

   function Why_Prog_Type_Of_Ada_Obj
     (N            : Node_Id;
      Is_Primitive : Boolean := False)
     return W_Simple_Value_Type_Id
   is
      Mutable : constant Boolean :=
                  not Is_Primitive and then Is_Mutable (N);
   begin
      return Why_Prog_Type_Of_Ada_Type (Etype (N), Mutable);
   end  Why_Prog_Type_Of_Ada_Obj;

end Gnat2Why.Types;
