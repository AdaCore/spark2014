------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                      W H Y - G E N - S C A L A R S                       --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                       Copyright (C) 2010-2012, AdaCore                   --
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

with Snames;             use Snames;
with Stand;              use Stand;

with Why.Conversions;    use Why.Conversions;
with Why.Atree.Builders; use Why.Atree.Builders;
with Why.Gen.Axioms;     use Why.Gen.Axioms;
with Why.Gen.Decl;       use Why.Gen.Decl;
with Why.Gen.Names;      use Why.Gen.Names;
with Why.Gen.Preds;      use Why.Gen.Preds;
with Why.Gen.Binders;    use Why.Gen.Binders;
with Why.Inter;          use Why.Inter;
with Why.Types;          use Why.Types;

package body Why.Gen.Scalars is

   procedure Define_Scalar_Conversions
     (Theory    : W_Theory_Declaration_Id;
      Why_Name  : W_Identifier_Id;
      Base_Type : EW_Scalar;
      Modulus   : W_Term_OId := Why_Empty);
   --  Given a type name, assuming that it ranges between First and Last,
   --  define conversions from this type to base type.

   procedure New_Boolean_Equality_Parameter
     (Theory   : W_Theory_Declaration_Id;
      Why_Name : W_Identifier_Id);
      --  Create a parameter of the form
      --     parameter <eq_param_name> : (m : type) -> (n : type) ->
      --        {} bool { if result then m = n else m <> n }

   -------------------------------------
   -- Declare_Ada_Abstract_Signed_Int --
   -------------------------------------

   procedure Declare_Ada_Abstract_Signed_Int
     (Theory  : W_Theory_Declaration_Id;
      Entity  : Entity_Id;
      First   : W_Integer_Constant_Id;
      Last    : W_Integer_Constant_Id;
      Modulus : W_Integer_Constant_Id)
   is
      Why_Id : constant W_Identifier_Id := To_Why_Id (Entity, Local => True);
   begin
      if Entity = Standard_Character then
         Emit (Theory,
               New_Type (Name => Why_Id,
                         Alias =>
                           New_Abstract_Type
                             (Name => To_Ident (WNE_Char_Type))));
      else
         Emit (Theory, New_Type (Name => Why_Id));
      end if;
      Define_Scalar_Attributes
        (Theory    => Theory,
         Base_Type => EW_Int,
         First     => +First,
         Last      => +Last,
         Modulus   => +Modulus);
      Define_Scalar_Conversions
        (Theory    => Theory,
         Why_Name  => Why_Id,
         Base_Type => EW_Int,
         Modulus   => +Modulus);
   end Declare_Ada_Abstract_Signed_Int;

   ----------------------
   -- Declare_Ada_Real --
   ----------------------

   procedure Declare_Ada_Real
     (Theory  : W_Theory_Declaration_Id;
      Entity  : Entity_Id;
      First   : W_Real_Constant_Id;
      Last    : W_Real_Constant_Id)
   is
      Why_Name : constant W_Identifier_Id := To_Why_Id (Entity, Local => True);
   begin
      Emit (Theory, New_Type (Name => Why_Name));
      Define_Scalar_Attributes
        (Theory    => Theory,
         Base_Type => EW_Real,
         First     => +First,
         Last      => +Last,
         Modulus   => Why_Empty);
      Define_Scalar_Conversions
        (Theory    => Theory,
         Why_Name  => Why_Name,
         Base_Type => EW_Real);
   end Declare_Ada_Real;

   -------------------------------
   -- Define_Scalar_Conversions --
   -------------------------------

   procedure Define_Scalar_Conversions
     (Theory    : W_Theory_Declaration_Id;
      Why_Name  : W_Identifier_Id;
      Base_Type : EW_Scalar;
      Modulus   : W_Term_OId := Why_Empty)
   is
      Arg_S    : constant W_Identifier_Id := New_Identifier (Name => "n");
      BT       : constant W_Primitive_Type_Id :=
        New_Base_Type (Base_Type => Base_Type);
      Abstr_Ty : constant W_Primitive_Type_Id :=
        New_Abstract_Type (Name => Why_Name);
      To_Id    : constant W_Identifier_Id := To_Ident (Convert_To (Base_Type));
   begin
      Define_Range_Predicate (Theory, Base_Type);

      --  to base type:
      Emit
        (Theory,
         New_Function_Decl
           (Domain      => EW_Term,
            Name        => To_Id,
            Binders        => New_Binders ((1 => Abstr_Ty)),
            Return_Type => BT));

      --  from base type:

      Emit
        (Theory,
         New_Function_Decl
           (Domain      => EW_Term,
            Name        => To_Ident (Convert_From (Base_Type)),
            Binders     => New_Binders ((1 => BT)),
            Return_Type => Abstr_Ty));

      --  range check
      declare
         Range_Check  : constant W_Pred_OId :=
                          New_Call
                            (Name   => To_Ident (WNE_Range_Pred),
                             Args   => (1 => +Arg_S));
         Range_Check_Post : constant W_Pred_Id :=
           New_Relation
             (Op_Type => Base_Type,
              Op      => EW_Eq,
              Left    => +To_Ident (WNE_Result),
              Right   => +Arg_S);
      begin
         Emit
           (Theory,
            New_Function_Decl
              (Domain      => EW_Prog,
               Name        => To_Ident (WNE_Range_Check_Fun),
               Binders     => (1 => (B_Name => Arg_S,
                                     B_Type => BT,
                                     others => <>)),
               Return_Type => BT,
               Pre         => Range_Check,
               Post        => Range_Check_Post));
      end;

      Define_Eq_Predicate (Theory, Why_Name, Base_Type);
      Define_Range_Axiom (Theory,
                          Why_Name,
                          To_Ident (Convert_To (Base_Type)));
      Define_Coerce_Axiom (Theory,
                           Base_Type,
                           Modulus);
      Define_Unicity_Axiom (Theory,
                            Why_Name,
                            Base_Type);
      New_Boolean_Equality_Parameter (Theory, Why_Name);
   end Define_Scalar_Conversions;

   ------------------------------
   -- Define_Scalar_Attributes --
   ------------------------------

   procedure Define_Scalar_Attributes
     (Theory     : W_Theory_Declaration_Id;
      Base_Type  : EW_Scalar;
      First      : W_Term_Id;
      Last       : W_Term_Id;
      Modulus    : W_Term_OId)
   is
      type Scalar_Attr is (S_First, S_Last, S_Modulus);

      type Attr_Info is record
         Attr_Id : Attribute_Id;
         Value   : W_Term_Id;
      end record;

      Attr_Values : constant array (Scalar_Attr) of Attr_Info :=
                      (S_First   => (Attribute_First, First),
                       S_Last    => (Attribute_Last, Last),
                       S_Modulus => (Attribute_Modulus, Modulus));
   begin
      for J in Attr_Values'Range loop
         declare
            Spec : Declaration_Spec;
         begin
            if Attr_Values (J).Value /= Why_Empty then
               Spec := (Kind   => W_Function_Def,
                        Domain => EW_Term,
                        Term   => Attr_Values (J).Value,
                        others => <>);
            else
               Spec := (Kind   => W_Function_Decl,
                        Domain => EW_Term,
                        others => <>);
            end if;
            Spec.Name := To_Ident (Attr_To_Why_Name (Attr_Values (J).Attr_Id));
            Emit_Top_Level_Declarations
              (Theory      => Theory,
               Binders     => (1 .. 0 => <>),
               Return_Type => New_Base_Type (Base_Type => Base_Type),
               Spec        => (1 => Spec));
         end;
      end loop;

      declare
         Arg_Name   : constant W_Identifier_Id := New_Identifier (Name => "x");
         BT         : constant W_Primitive_Type_Id :=
                        New_Base_Type (Base_Type => Base_Type);
         Why_Str    : constant W_Primitive_Type_Id :=
                        New_Abstract_Type (Name => To_Ident (WNE_String));
      begin
         Emit (Theory,
               New_Function_Decl
                 (Domain      => EW_Term,
                  Name        => To_Ident (Attr_To_Why_Name (Attribute_Image)),
                  Binders     => (1 => (B_Name => Arg_Name,
                                        B_Type => BT,
                                        others => <>)),
                  Return_Type => Why_Str));

         Emit (Theory,
               New_Function_Decl
                 (Domain      => EW_Pred,
                  Name        => To_Ident (WNE_Attr_Value_Pre_Check),
                  Binders     => (1 => (B_Name => Arg_Name,
                                        B_Type => Why_Str,
                                        others => <>)),
                  Return_Type => New_Base_Type (Base_Type => EW_Prop)));

         Emit (Theory,
               New_Function_Decl
                 (Domain      => EW_Term,
                  Name        => To_Ident (Attr_To_Why_Name (Attribute_Value)),
                  Binders     => (1 => (B_Name => Arg_Name,
                                        B_Type => Why_Str,
                                        others => <>)),
                  Return_Type => BT));

         Emit (Theory,
               New_Function_Decl
                 (Domain      => EW_Prog,
                  Name        =>
                    To_Program_Space
                      (To_Ident (Attr_To_Why_Name (Attribute_Value))),
                  Binders     => (1 => (B_Name => Arg_Name,
                                        B_Type => Why_Str,
                                        others => <>)),
                  Return_Type => BT,
                  Pre         =>
                    New_Call (Name   => To_Ident (WNE_Attr_Value_Pre_Check),
                              Args   => (1 => +Arg_Name))));
      end;
   end Define_Scalar_Attributes;

   ------------------------------------
   -- New_Boolean_Equality_Parameter --
   ------------------------------------

   procedure New_Boolean_Equality_Parameter
     (Theory   : W_Theory_Declaration_Id;
      Why_Name : W_Identifier_Id)
   is
      Arg_S    : constant W_Identifier_Id := New_Identifier (Name => "n");
      Arg_T    : constant W_Identifier_Id := New_Identifier (Name => "m");
      True_Term : constant W_Term_Id :=
                  New_Literal (Value => EW_True);
      Cond     : constant W_Pred_Id :=
                  New_Relation
                     (Left    => +To_Ident (WNE_Result),
                      Op_Type => EW_Bool,
                      Right   => +True_Term,
                      Op      => EW_Eq);
      Then_Rel : constant W_Pred_Id :=
                 New_Relation
                   (Op      => EW_Eq,
                    Op_Type => EW_Bool,
                    Left    => +Arg_S,
                    Right   => +Arg_T);
      Else_Rel : constant W_Pred_Id :=
                 New_Relation
                   (Op      => EW_Ne,
                    Op_Type => EW_Bool,
                    Left    => +Arg_S,
                    Right   => +Arg_T);
      Post    : constant W_Pred_Id :=
                  New_Conditional
                    (Condition => +Cond,
                     Then_Part => +Then_Rel,
                     Else_Part => +Else_Rel);
      Pre     : constant W_Pred_Id :=
                  New_Literal (Value => EW_True);
      Arg_Type : constant W_Primitive_Type_Id :=
        New_Abstract_Type (Name => Why_Name);
   begin
      Emit
        (Theory,
         New_Function_Decl
           (Domain      => EW_Prog,
            Name        => To_Program_Space (To_Ident (WNE_Bool_Eq)),
            Binders     =>
              (1 =>
                 (B_Name => Arg_S,
                  B_Type => Arg_Type,
                  others => <>),
               2 =>
                 (B_Name => Arg_T,
                  B_Type => Arg_Type,
                  others => <>)),
            Return_Type => New_Base_Type (Base_Type => EW_Bool),
            Pre         => Pre,
            Post        => Post));
   end New_Boolean_Equality_Parameter;

end Why.Gen.Scalars;
