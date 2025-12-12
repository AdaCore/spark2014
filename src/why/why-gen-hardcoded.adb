------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                    W H Y - G E N - H A R D C O D E D                     --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                     Copyright (C) 2020-2025, AdaCore                     --
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

with Common_Containers;   use Common_Containers;
with Errout_Wrapper;      use Errout_Wrapper;
with GNAT.Source_Info;
with GNATCOLL.Symbols;    use GNATCOLL.Symbols;
with Namet;               use Namet;
with Snames;              use Snames;
with SPARK_Util.Types;    use SPARK_Util.Types;
with Stand;               use Stand;
with Stringt;             use Stringt;
with Uintp;               use Uintp;
with Urealp;              use Urealp;
with VC_Kinds;            use VC_Kinds;
with Why.Atree.Accessors; use Why.Atree.Accessors;
with Why.Atree.Builders;  use Why.Atree.Builders;
with Why.Atree.Modules;   use Why.Atree.Modules;
with Why.Conversions;     use Why.Conversions;
with Why.Gen.Decl;        use Why.Gen.Decl;
with Why.Gen.Expr;        use Why.Gen.Expr;
with Why.Gen.Names;       use Why.Gen.Names;
with Why.Gen.Progs;       use Why.Gen.Progs;
with Why.Inter;           use Why.Inter;
with Why.Types;           use Why.Types;

package body Why.Gen.Hardcoded is
   package BIN renames Big_Integers_Names;
   use BIN;
   package BRN renames Big_Reals_Names;
   use BRN;
   package EFN renames Elementary_Functions_Names;
   use EFN;
   package SSEN renames System_Storage_Elements_Names;
   use SSEN;

   function Uint_From_String (Str_Value : String) return Uint;
   --  Read an integer value from a string. Might raise Constraint_Error.

   type M_Real_Time (Initialized : Boolean := False) is record
      case Initialized is
         when False =>
            null;

         when True =>
            Module        : W_Module_Id;
            T             : W_Type_Id;
            Of_Int        : W_Identifier_Id;
            To_Duration   : W_Identifier_Id;
            Of_Duration   : W_Identifier_Id;
            Time_Of       : W_Identifier_Id;
            Split         : W_Identifier_Id;
            Time_First    : W_Identifier_Id;
            Time_Last     : W_Identifier_Id;
            In_Range_Time : W_Identifier_Id;
            Span_First    : W_Identifier_Id;
            Span_Last     : W_Identifier_Id;
            In_Range_Span : W_Identifier_Id;
      end case;
   end record;

   Real_Time_Module : M_Real_Time;

   -----------------------------------------
   -- Dynamic_Property_For_Hardcoded_Type --
   -----------------------------------------

   function Dynamic_Property_For_Hardcoded_Type
     (E : Type_Kind_Id; Expr : W_Term_Id) return W_Pred_Id is
   begin
      if Is_From_Hardcoded_Unit (E, Real_Time) then
         return
           New_Call
             (Name =>
                (if Get_Name_String (Chars (E)) = Real_Time_Names.Time
                 then Real_Time_Module.In_Range_Time
                 elsif Get_Name_String (Chars (E)) = Real_Time_Names.Time_Span
                 then Real_Time_Module.In_Range_Span
                 else raise Program_Error),
              Args => (1 => +Expr));
      else
         return True_Pred;
      end if;
   end Dynamic_Property_For_Hardcoded_Type;

   -------------------------------------
   -- Emit_Hardcoded_Type_Declaration --
   -------------------------------------

   procedure Emit_Hardcoded_Type_Declaration (Th : Theory_UC; E : Entity_Id) is
      Alias : W_Type_Id;
   begin
      --  The Why3 type used to represent the type is stored in Alias
      --  The following case statement is meant to be extended in the
      --  future.

      case Get_Hardcoded_Unit (E) is
         when Big_Integers =>
            Alias := EW_Int_Type;

         when Big_Reals    =>
            Alias := EW_Real_Type;

         when Real_Time    =>

            --  If necessary, initialize Real_Time_Module as a clone of
            --  Real_Time_Model. It takes as parameters the numerator and
            --  denominator of Time_Unit as well as those of the small of
            --  Duration for conversions.

            if not Real_Time_Module.Initialized then
               declare
                  Module   : constant W_Module_Id :=
                    New_Module
                      (File => No_Symbol, Name => "Ada__real_time__model");
                  N_Ty     : constant W_Type_Id :=
                    New_Type
                      (Is_Mutable => False,
                       Type_Kind  => EW_Builtin,
                       Name       => Get_Name (M_Main.Fixed_Type));
                  M_Module : constant M_Real_Time :=
                    M_Real_Time'
                      (Initialized   => True,
                       Module        => Module,
                       T             => N_Ty,
                       Of_Int        =>
                         New_Identifier
                           (Module => Module,
                            Domain => EW_Term,
                            Symb   => NID ("of_int"),
                            Typ    => N_Ty),
                       To_Duration   =>
                         New_Identifier
                           (Module => Module,
                            Domain => EW_Term,
                            Symb   => NID ("to_duration"),
                            Typ    => EW_Fixed_Type (Standard_Duration)),
                       Of_Duration   =>
                         New_Identifier
                           (Module => Module,
                            Domain => EW_Term,
                            Symb   => NID ("of_duration"),
                            Typ    => N_Ty),
                       Time_Of       =>
                         New_Identifier
                           (Module => Module,
                            Domain => EW_Term,
                            Symb   => NID ("time_of"),
                            Typ    => N_Ty),
                       Split         =>
                         New_Identifier
                           (Module => Module,
                            Domain => EW_Pred,
                            Symb   => NID ("split")),
                       Time_First    =>
                         New_Identifier
                           (Module => Module,
                            Domain => EW_Term,
                            Symb   => NID ("time_first"),
                            Typ    => N_Ty),
                       Time_Last     =>
                         New_Identifier
                           (Module => Module,
                            Domain => EW_Term,
                            Symb   => NID ("time_last"),
                            Typ    => N_Ty),
                       In_Range_Time =>
                         New_Identifier
                           (Module => Module,
                            Domain => EW_Pred,
                            Symb   => NID ("in_range_time")),
                       Span_First    =>
                         New_Identifier
                           (Module => Module,
                            Domain => EW_Term,
                            Symb   => NID ("span_first"),
                            Typ    => N_Ty),
                       Span_Last     =>
                         New_Identifier
                           (Module => Module,
                            Domain => EW_Term,
                            Symb   => NID ("span_last"),
                            Typ    => N_Ty),
                       In_Range_Span =>
                         New_Identifier
                           (Module => Module,
                            Domain => EW_Pred,
                            Symb   => NID ("in_range_span")));

                  --  Time and Time_Span are fixed point type with the same
                  --  small.

                  Num_Small : constant W_Name_Id :=
                    New_Name (Symb => NID ("num_small"));
                  Den_Small : constant W_Name_Id :=
                    New_Name (Symb => NID ("den_small"));

                  --  The numerator and denominator of Time and Time_Span are
                  --  queried from Time_Unit.

                  Time_Unit   : constant Ureal := Get_Real_Time_Time_Unit (E);
                  Num_Small_V : constant W_Term_OId :=
                    New_Integer_Constant (Value => Norm_Num (Time_Unit));
                  Den_Small_V : constant W_Term_OId :=
                    New_Integer_Constant (Value => Norm_Den (Time_Unit));

                  --  The small of Duration is used to encode conversions

                  D_Num_Small : constant W_Name_Id :=
                    New_Name (Symb => NID ("num_small_duration"));
                  D_Den_Small : constant W_Name_Id :=
                    New_Name (Symb => NID ("den_small_duration"));

                  --  The numerator and denominator of Duration depend on the
                  --  plateform. They are passed as additional parameters to
                  --  the clone.

                  D_Small       : constant Ureal :=
                    Small_Value (Standard_Duration);
                  D_Num_Small_V : constant W_Term_OId :=
                    New_Integer_Constant (Value => Norm_Num (D_Small));
                  D_Den_Small_V : constant W_Term_OId :=
                    New_Integer_Constant (Value => Norm_Den (D_Small));

                  Subst : W_Clone_Substitution_Array (1 .. 4);
                  Th    : Theory_UC;

               begin
                  Th :=
                    Open_Theory
                      (WF_Context,
                       Module,
                       Comment =>
                         "Module for Ada.Real_Time, created in "
                         & GNAT.Source_Info.Enclosing_Entity);

                  Emit
                    (Th,
                     Why.Atree.Builders.New_Function_Decl
                       (Domain      => EW_Term,
                        Name        => New_Identifier (Num_Small),
                        Binders     => (1 .. 0 => <>),
                        Return_Type => EW_Int_Type,
                        Labels      => Symbol_Sets.Empty_Set,
                        Location    => No_Location,
                        Def         => +Num_Small_V));
                  Emit
                    (Th,
                     Why.Atree.Builders.New_Function_Decl
                       (Domain      => EW_Term,
                        Name        => New_Identifier (Den_Small),
                        Binders     => (1 .. 0 => <>),
                        Return_Type => EW_Int_Type,
                        Labels      => Symbol_Sets.Empty_Set,
                        Location    => No_Location,
                        Def         => +Den_Small_V));
                  Emit
                    (Th,
                     Why.Atree.Builders.New_Function_Decl
                       (Domain      => EW_Term,
                        Name        => New_Identifier (D_Num_Small),
                        Binders     => (1 .. 0 => <>),
                        Return_Type => EW_Int_Type,
                        Labels      => Symbol_Sets.Empty_Set,
                        Location    => No_Location,
                        Def         => +D_Num_Small_V));
                  Emit
                    (Th,
                     Why.Atree.Builders.New_Function_Decl
                       (Domain      => EW_Term,
                        Name        => New_Identifier (D_Den_Small),
                        Binders     => (1 .. 0 => <>),
                        Return_Type => EW_Int_Type,
                        Labels      => Symbol_Sets.Empty_Set,
                        Location    => No_Location,
                        Def         => +D_Den_Small_V));

                  Subst :=
                    (1 =>
                       New_Clone_Substitution
                         (Kind      => EW_Function,
                          Orig_Name => Num_Small,
                          Image     => Num_Small),
                     2 =>
                       New_Clone_Substitution
                         (Kind      => EW_Function,
                          Orig_Name => Den_Small,
                          Image     => Den_Small),
                     3 =>
                       New_Clone_Substitution
                         (Kind      => EW_Function,
                          Orig_Name => D_Num_Small,
                          Image     => D_Num_Small),
                     4 =>
                       New_Clone_Substitution
                         (Kind      => EW_Function,
                          Orig_Name => D_Den_Small,
                          Image     => D_Den_Small));

                  Emit
                    (Th,
                     New_Clone_Declaration
                       (Theory_Kind   => EW_Theory,
                        Clone_Kind    => EW_Export,
                        Origin        => Real_Time_Model,
                        As_Name       => No_Symbol,
                        Substitutions => Subst));

                  Close_Theory (Th, Kind => Definition_Theory);
                  Real_Time_Module := M_Module;
               end;
            end if;

            Alias := Real_Time_Module.T;

         --  No types are declared in the following units

         when Cut_Operations
            | System_Storage_Elements
            | Elementary_Functions
            | System       =>
            raise Program_Error;
      end case;

      pragma Assert (Is_Simple_Private_Type (Retysp (E)));

      Emit (Th, New_Type_Decl (Name => To_Name (WNE_Rec_Rep), Alias => Alias));

   end Emit_Hardcoded_Type_Declaration;

   -----------------------------
   -- Is_Hardcoded_Comparison --
   -----------------------------

   function Is_Hardcoded_Comparison (Subp : Entity_Id) return Boolean
   is (Is_Subprogram (Subp)
       and then Is_Hardcoded_Entity (Subp)
       and then
         Chars (Subp)
         in Name_Op_Eq | Name_Op_Lt | Name_Op_Le | Name_Op_Gt | Name_Op_Ge);

   ----------------------------
   -- Is_Hardcoded_Operation --
   ----------------------------

   function Is_Hardcoded_Operation
     (Op : N_Binary_Op; Left, Right : Type_Kind_Id) return Boolean
   is (Op = N_Op_Mod
       and then Is_System_Address (Left)
       and then Has_Stoele_Offset (Right));

   ------------------------------
   -- Hardcoded_Constant_Value --
   ------------------------------

   function Hardcoded_Constant_Value (E : E_Constant_Id) return W_Term_Id is
   begin
      if Is_From_Hardcoded_Unit (E, Real_Time) then
         if Get_Name_String (Chars (E)) = Real_Time_Names.Time_First then
            return +Real_Time_Module.Time_First;
         elsif Get_Name_String (Chars (E)) = Real_Time_Names.Time_Last then
            return +Real_Time_Module.Time_Last;
         elsif Get_Name_String (Chars (E)) = Real_Time_Names.Time_Span_First
         then
            return +Real_Time_Module.Span_First;
         elsif Get_Name_String (Chars (E)) = Real_Time_Names.Time_Span_Last
         then
            return +Real_Time_Module.Span_Last;
         elsif Get_Name_String (Chars (E)) = Real_Time_Names.Time_Span_Zero
         then
            return
              New_Fixed_Constant (Value => Uint_0, Typ => Real_Time_Module.T);
         elsif Get_Name_String (Chars (E)) = Real_Time_Names.Time_Span_Unit
         then
            return
              New_Fixed_Constant (Value => Uint_1, Typ => Real_Time_Module.T);
         else
            raise Program_Error;
         end if;
      else
         raise Program_Error;
      end if;
   end Hardcoded_Constant_Value;

   ----------------------------
   -- New_Hardcoded_Equality --
   ----------------------------

   function Hardcoded_Equality_Symbol (Typ : Entity_Id) return W_Identifier_Id
   is
   begin
      case Get_Hardcoded_Unit (Typ) is
         when Big_Integers =>
            return M_Integer.Bool_Eq;

         when Big_Reals    =>
            return M_Real.Bool_Eq;

         when Real_Time    =>
            return M_Integer.Bool_Eq;

         --  No equal in the following units

         when Cut_Operations
            | System_Storage_Elements
            | Elementary_Functions
            | System       =>
            raise Program_Error;

      end case;
   end Hardcoded_Equality_Symbol;

   -------------------------------------------
   -- Hardcoded_Type_Needs_Dynamic_Property --
   -------------------------------------------

   function Hardcoded_Type_Needs_Dynamic_Property
     (E : Type_Kind_Id) return Boolean
   is (Is_From_Hardcoded_Unit (E, Real_Time));

   ---------------------------------------
   -- Transform_Hardcoded_Function_Call --
   ---------------------------------------

   function Transform_Hardcoded_Function_Call
     (Subp     : Entity_Id;
      Args     : W_Expr_Array;
      Domain   : EW_Domain;
      Ada_Node : Node_Id) return W_Expr_Id
   is
      T           : W_Expr_Id := Why_Empty;
      Name_String : constant String := Get_Name_String (Chars (Subp));

   begin
      --  Cut operations are translated specifically depending on the context

      if Is_From_Hardcoded_Unit (Subp, Cut_Operations) then
         raise Program_Error;

      --  Conversion functions are translated in the same way in
      --  the Big_Integers package and its generic subpackages.

      elsif (Is_From_Hardcoded_Generic_Unit (Subp, Big_Integers)
             and then
               Name_String
               in BIN.Generic_To_Big_Integer | BIN.Generic_From_Big_Integer)
        or else
          (Is_From_Hardcoded_Unit (Subp, Big_Integers)
           and then Name_String in BIN.To_Big_Integer | BIN.To_Integer)
      then

         --  Conversion from an integer type to type Big_Integer, no check
         --  needed.

         if Name_String in BIN.Generic_To_Big_Integer | BIN.To_Big_Integer then
            T :=
              Insert_Simple_Conversion
                (Ada_Node => Ada_Node,
                 Domain   => Domain,
                 Expr     => Args (1),
                 To       => EW_Int_Type);

            --  Big_Integer is an alias of int in Why3, but in GNAT2why,
            --  they are different types. We reestablish the proper type
            --  in the AST by adding a dummy node.

            T :=
              New_Label
                (Labels => Symbol_Sets.Empty_Set,
                 Def    => T,
                 Domain => Domain,
                 Typ    => Type_Of_Node (Etype (Subp)));

         --  Conversion from a Big_Integer to an integer type

         elsif Name_String in BIN.Generic_From_Big_Integer | BIN.To_Integer
         then

            T :=
              Insert_Simple_Conversion
                (Ada_Node => Ada_Node,
                 Domain   => Domain,
                 Expr     =>
                   New_Label
                     (Ada_Node => Ada_Node,
                      Domain   => Domain,
                      Labels   => Symbol_Sets.Empty_Set,
                      Def      => Args (1),
                      Typ      => EW_Int_Type),
                 To       => Type_Of_Node (Etype (Subp)));

            --  A check is needed when in the program domain. We don't use
            --  Insert_Checked_Conversion because it relies on frontend flags
            --  to insert checks on scalar conversions. These flags are not
            --  set for these conversions.

            if Domain = EW_Prog then
               T :=
                 +Sequence
                    (Ada_Node => Ada_Node,
                     Left     =>
                       New_Ignore
                         (Ada_Node => Ada_Node,
                          Prog     =>
                            Do_Range_Check
                              (Ada_Node   => Ada_Node,
                               Ty         => Type_Of_Node (Etype (Subp)),
                               W_Expr     =>

                               --  Do_Range_Check takes integer types in entry,
                               --  but in GNAT2why, Big_Integer is not an
                               --  integer type. We add this dummy node to
                               --  treat Args (1) as an integer type in
                               --  Do_Range_Check.

                                   New_Label
                                      (Ada_Node => Ada_Node,
                                       Domain   => Domain,
                                       Labels   => Symbol_Sets.Empty_Set,
                                       Def      => Args (1),
                                       Typ      => EW_Int_Type),
                               Check_Kind => RCK_Range)),
                     Right    => +T);
            end if;
         end if;

      --  Transformation of the other functions in Big_Integers

      elsif Is_From_Hardcoded_Unit (Subp, Big_Integers) then

         --  This block transforms the comparison operators, binary operators,
         --  Min, Max and Greatest_Common_Divisor.

         if Args'Length = 2 then

            declare
               Base      : constant W_Type_Id := Type_Of_Node (Etype (Subp));
               Left_Rep  : constant W_Expr_Id := Args (1);
               Right_Rep : constant W_Expr_Id :=
                 (if Chars (Subp) = Name_Op_Expon
                  then
                    Insert_Simple_Conversion
                      (Ada_Node => Ada_Node,
                       Domain   => Domain,
                       Expr     => Args (2),
                       To       => EW_Int_Type)
                  else Args (2));
               Name      : W_Identifier_Id;
            begin

               --  The following block assigns a value to Name which will be
               --  called in New_Call afterwards.

               if Name_String = BIN.Min then
                  Name := M_Int_Minmax.Min;

               elsif Name_String = BIN.Max then
                  Name := M_Int_Minmax.Max;

               elsif Name_String = BIN.Gcd then
                  Name := M_Int_Gcd.Gcd;

               else
                  case Chars (Subp) is
                     when Name_Op_Add      =>
                        Name := Int_Infix_Add;

                     when Name_Op_Subtract =>
                        Name := Int_Infix_Subtr;

                     when Name_Op_Multiply =>
                        Name := Int_Infix_Mult;

                     when Name_Op_Divide   =>
                        Name := M_Int_Div.Div;

                     when Name_Op_Mod      =>
                        Name := M_Int_Div.Mod_Id;

                     when Name_Op_Rem      =>
                        Name := M_Int_Div.Rem_Id;

                     when Name_Op_Expon    =>
                        Name := M_Int_Power.Power;

                     when Name_Op_Eq       =>
                        Name :=
                          (if Domain = EW_Term
                           then M_Integer.Bool_Eq
                           else Why_Eq);

                     when Name_Op_Lt       =>
                        Name :=
                          (if Domain = EW_Term
                           then M_Integer.Bool_Lt
                           else Int_Infix_Lt);

                     when Name_Op_Le       =>
                        Name :=
                          (if Domain = EW_Term
                           then M_Integer.Bool_Le
                           else Int_Infix_Le);

                     when Name_Op_Gt       =>
                        Name :=
                          (if Domain = EW_Term
                           then M_Integer.Bool_Gt
                           else Int_Infix_Gt);

                     when Name_Op_Ge       =>
                        Name :=
                          (if Domain = EW_Term
                           then M_Integer.Bool_Ge
                           else Int_Infix_Ge);

                     when others           =>
                        raise Program_Error;
                  end case;
               end if;

               --  Divide, Mod, Rem and Gcd need a division or precondition
               --  check.

               declare
                  Check : constant Boolean :=
                    Domain = EW_Prog
                    and then
                      (Chars (Subp)
                       in Name_Op_Divide | Name_Op_Mod | Name_Op_Rem
                       or else Name_String = BIN.Gcd);
                  pragma Assert (if Check then Present (Ada_Node));

                  Check_Info : Check_Info_Type := New_Check_Info;
                  Reason     : VC_Kind := VC_Precondition;

               begin
                  --  For Divide, Mod, and Rem, emit a division check instead
                  --  of a precondition check.

                  if Name_String /= BIN.Gcd then
                     Check_Info.Fix_Info.Divisor := Get_Ada_Node (+Args (2));
                     Reason := VC_Division_Check;
                  end if;

                  T :=
                    New_Operator_Call
                      (Ada_Node   => Ada_Node,
                       Domain     => Domain,
                       Name       => Name,
                       Args       => (1 => Left_Rep, 2 => Right_Rep),
                       Reason     => Reason,
                       Check_Info => Check_Info,
                       Check      => Check,
                       Typ        => Base);
               end;
            end;

         --  This block transforms the unary operators, Is_Valid, and
         --  From_String.

         elsif Args'Length = 1 then

            --  Is_Valid is handled as the attribute 'Valid

            if Name_String = BIN.Is_Valid and then Args'Length = 1 then
               pragma Assert (Args'Length = 1);
               Error_Msg_N
                 (Warning_Message (Warn_Function_Is_Valid),
                  Ada_Node,
                  First => True,
                  Kind  => Warning_Kind);

               if Domain = EW_Prog then
                  T :=
                    +Sequence
                       (Ada_Node => Ada_Node,
                        Left     => New_Ignore (Prog => +Args (1)),
                        Right    => True_Prog);
               else
                  T :=
                    Why.Conversions."+"
                      (New_Literal (Value => EW_True, Domain => Domain));
               end if;

            --  Imprecise translation of From_String. This is a function taking
            --  a string representing an integer value.
            --  We translate From_String (Val) as:
            --    int_value (of_string (val))
            --  This translation is imprecise as int_value and of_string are
            --  abstract Why3 functions left mostly uninterpreted.
            --  In the special case where Val is a string literal, a more
            --  precise translation is attempted first, see
            --  Transform_Hardcoded_Literal.

            elsif Name_String = BIN.From_String then
               T :=
                 New_Call
                   (Ada_Node => Ada_Node,
                    Domain   => Domain,
                    Name     => Of_String_Id,
                    Args     => (1 => Args (1)));

               T :=
                 New_Operator_Call
                   (Ada_Node => Ada_Node,
                    Domain   => Domain,
                    Name     => M_Builtin_From_Image.Int_Value,
                    Args     => (1 => T),
                    Reason   => VC_Precondition,
                    Check    => Domain = EW_Prog,
                    Typ      => EW_Int_Type);

               T :=
                 New_Label
                   (Ada_Node => Ada_Node,
                    Domain   => Domain,
                    Labels   => Symbol_Sets.Empty_Set,
                    Def      => T,
                    Typ      => Type_Of_Node (Etype (Subp)));

            elsif Chars (Subp) = Name_Op_Add then
               T := Args (1);
            else
               declare
                  Base : constant W_Type_Id := Type_Of_Node (Etype (Subp));
                  Name : W_Identifier_Id;
               begin
                  case Chars (Subp) is
                     when Name_Op_Subtract =>
                        Name := Int_Unary_Minus;

                     when Name_Op_Abs      =>
                        Name := M_Int_Abs.Abs_Id;

                     when others           =>
                        raise Program_Error;
                  end case;

                  T :=
                    New_Call
                      (Domain   => Domain,
                       Ada_Node => Ada_Node,
                       Name     => Name,
                       Args     => (1 => Args (1)),
                       Typ      => Base);
               end;
            end if;

         else
            raise Program_Error;
         end if;

      --  Transformation of Big_Reals

      elsif Is_From_Hardcoded_Unit (Subp, Big_Reals) then
         if Args'Length = 2 then

            --  Imprecise translation of From_Universal_Image. This is a
            --  function taking two strings representing integer values
            --  standing for the numerator and denominator of a big real.
            --  We translate From_Universal_Value (Num, Den) as:
            --    to_real (int_value (of_string (num))) /
            --      to_real (int_value (of_string (den)))
            --  This translation is imprecise as int_value and of_string are
            --  both abstract Why3 functions left mostly uninterpreted.
            --  In the special case where Num and Den are string literals, a
            --  more precise translation is attempted first, see
            --  Transform_Hardcoded_Literal.

            if Name_String = BRN.From_Universal_Image then
               declare
                  Num : W_Expr_Id :=
                    New_Call
                      (Ada_Node => Ada_Node,
                       Domain   => Domain,
                       Name     => Of_String_Id,
                       Args     => (1 => Args (1)));
                  Den : W_Expr_Id :=
                    New_Call
                      (Ada_Node => Ada_Node,
                       Domain   => Domain,
                       Name     => Of_String_Id,
                       Args     => (1 => Args (2)));

               begin
                  --  Translate each operand from an image to an integer

                  Num :=
                    New_Operator_Call
                      (Ada_Node => Ada_Node,
                       Domain   => Domain,
                       Name     => M_Builtin_From_Image.Int_Value,
                       Args     => (1 => Num),
                       Reason   => VC_Precondition,
                       Check    => Domain = EW_Prog,
                       Typ      => EW_Int_Type);
                  Den :=
                    New_Operator_Call
                      (Ada_Node => Ada_Node,
                       Domain   => Domain,
                       Name     => M_Builtin_From_Image.Int_Value,
                       Args     => (1 => Den),
                       Reason   => VC_Precondition,
                       Check    => Domain = EW_Prog,
                       Typ      => EW_Int_Type);

                  --  Insert a conversion to real on both operands

                  Num :=
                    New_Call
                      (Domain   => Domain,
                       Ada_Node => Ada_Node,
                       Name     => M_Real_From_Int.From_Int,
                       Args     => (1 => Num));
                  Den :=
                    New_Call
                      (Domain   => Domain,
                       Ada_Node => Ada_Node,
                       Name     => M_Real_From_Int.From_Int,
                       Args     => (1 => Den));

                  --  Reconstruct the real value by doing the division

                  T :=
                    New_Operator_Call
                      (Ada_Node   => Ada_Node,
                       Domain     => Domain,
                       Name       => Real_Infix_Div,
                       Fix_Name   => True,
                       Args       => (1 => Num, 2 => Den),
                       Reason     => VC_Division_Check,
                       Check_Info =>
                         New_Check_Info (Divisor => Get_Ada_Node (+Args (2))),
                       Check      => Domain = EW_Prog,
                       Typ        => EW_Real_Type);

                  T :=
                    New_Label
                      (Ada_Node => Ada_Node,
                       Domain   => Domain,
                       Labels   => Symbol_Sets.Empty_Set,
                       Def      => T,
                       Typ      => Type_Of_Node (Etype (Subp)));
               end;

            --  This block transforms the comparison operators, binary
            --  operators, Min, and Max.

            else
               declare
                  Base      : constant W_Type_Id :=
                    Type_Of_Node (Etype (Subp));
                  Left_Rep  : W_Expr_Id := Args (1);
                  Right_Rep : W_Expr_Id := Args (2);
                  Name      : W_Identifier_Id;
               begin

                  --  The following block assigns a value to Name which will be
                  --  called in New_Call afterwards.

                  if Name_String = BRN.Min then
                     Name := M_Real_Minmax.Min;

                  elsif Name_String = BIN.Max then
                     Name := M_Real_Minmax.Max;

                  else
                     case Chars (Subp) is
                        when Name_Op_Add      =>
                           Name := Real_Infix_Add;

                        when Name_Op_Subtract =>
                           Name := Real_Infix_Subtr;

                        when Name_Op_Multiply =>
                           Name := Real_Infix_Mult;

                        when Name_Op_Divide   =>
                           --  If the division is done on big integers, we need
                           --  to insert a conversion to real on both operands.

                           if Is_From_Hardcoded_Unit
                                (Root_Retysp (Etype (First_Formal (Subp))),
                                 Big_Integers)
                           then
                              Left_Rep :=
                                New_Call
                                  (Domain   => Domain,
                                   Ada_Node => Ada_Node,
                                   Name     => M_Real_From_Int.From_Int,
                                   Args     => (1 => Left_Rep));
                              Right_Rep :=
                                New_Call
                                  (Domain   => Domain,
                                   Ada_Node => Ada_Node,
                                   Name     => M_Real_From_Int.From_Int,
                                   Args     => (1 => Right_Rep));
                           end if;

                           Name := Real_Infix_Div;

                        when Name_Op_Expon    =>
                           --  For exponentiation, a mathematical integer is
                           --  expected for the second parameter.

                           Right_Rep :=
                             Insert_Simple_Conversion
                               (Ada_Node => Ada_Node,
                                Domain   => Domain,
                                Expr     => Right_Rep,
                                To       => EW_Int_Type);
                           Name := M_Real_Power.Power;

                        when Name_Op_Eq       =>
                           Name :=
                             (if Domain = EW_Term
                              then M_Real.Bool_Eq
                              elsif Domain = EW_Pred
                              then Why_Eq
                              else Real_Infix_Eq);

                        when Name_Op_Lt       =>
                           Name :=
                             (if Domain = EW_Term
                              then M_Real.Bool_Lt
                              else Real_Infix_Lt);

                        when Name_Op_Le       =>
                           Name :=
                             (if Domain = EW_Term
                              then M_Real.Bool_Le
                              else Real_Infix_Le);

                        when Name_Op_Gt       =>
                           Name :=
                             (if Domain = EW_Term
                              then M_Real.Bool_Gt
                              else Real_Infix_Gt);

                        when Name_Op_Ge       =>
                           Name :=
                             (if Domain = EW_Term
                              then M_Real.Bool_Ge
                              else Real_Infix_Ge);

                        when others           =>
                           raise Program_Error;
                     end case;
                  end if;

                  --  Divide needs a division check

                  declare
                     Check : constant Boolean :=
                       Domain = EW_Prog and then Chars (Subp) = Name_Op_Divide;
                  begin
                     pragma Assert (if Check then Present (Ada_Node));

                     T :=
                       New_Operator_Call
                         (Ada_Node   => Ada_Node,
                          Domain     => Domain,
                          Name       => Name,
                          Fix_Name   => True,
                          Args       => (1 => Left_Rep, 2 => Right_Rep),
                          Reason     => VC_Division_Check,
                          Check_Info =>
                            New_Check_Info
                              (Divisor => Get_Ada_Node (+Args (2))),
                          Check      => Check,
                          Typ        => Base);
                  end;
               end;
            end if;

         --  This block transforms the unary operators, Is_Valid, and
         --  From_[Quotient_]String.

         elsif Args'Length = 1 then

            --  Is_Valid is handled as the attribute 'Valid

            if Name_String = BRN.Is_Valid and then Args'Length = 1 then
               pragma Assert (Args'Length = 1);
               Error_Msg_N
                 (Warning_Message (Warn_Function_Is_Valid),
                  Ada_Node,
                  First => True,
                  Kind  => Warning_Kind);

               if Domain = EW_Prog then
                  T :=
                    +Sequence
                       (Ada_Node => Ada_Node,
                        Left     => New_Ignore (Prog => +Args (1)),
                        Right    => True_Prog);
               else
                  T := Bool_True (Domain);
               end if;

            --  Imprecise translation of From_[Quotient_]String. This is a
            --  function taking a string representing a real value. We
            --  translate From_[Quotient_]String (Val) as:
            --    real_[quotient_]value (of_string (val))
            --  This translation is imprecise as real_value and of_string are
            --  abstract Why3 functions left mostly uninterpreted. In the
            --  special case where Val is a string literal, a more precise
            --  translation is attempted first, see
            --  Transform_Hardcoded_Literal.

            elsif Name_String = BRN.From_String
              or else Name_String = BRN.From_Quotient_String
            then
               T :=
                 New_Call
                   (Ada_Node => Ada_Node,
                    Domain   => Domain,
                    Name     => Of_String_Id,
                    Args     => (1 => Args (1)));

               T :=
                 New_Operator_Call
                   (Ada_Node => Ada_Node,
                    Domain   => Domain,
                    Name     =>
                      (if Name_String = BRN.From_String
                       then M_Builtin_From_Image.Real_Value
                       else M_Builtin_From_Image.Real_Quotient_Value),
                    Args     => (1 => T),
                    Reason   => VC_Precondition,
                    Check    => Domain = EW_Prog,
                    Typ      => EW_Real_Type);

               T :=
                 New_Label
                   (Ada_Node => Ada_Node,
                    Domain   => Domain,
                    Labels   => Symbol_Sets.Empty_Set,
                    Def      => T,
                    Typ      => Type_Of_Node (Etype (Subp)));

            elsif Chars (Subp) = Name_Op_Add then
               T := Args (1);
            else
               declare
                  Base : constant W_Type_Id := Type_Of_Node (Etype (Subp));
                  Name : W_Identifier_Id;
               begin
                  case Chars (Subp) is
                     when Name_Op_Subtract =>
                        Name := Real_Unary_Minus;

                     when Name_Op_Abs      =>
                        Name := M_Real_Abs.Abs_Id;

                     when others           =>
                        raise Program_Error;
                  end case;

                  T :=
                    New_Call
                      (Domain   => Domain,
                       Ada_Node => Ada_Node,
                       Name     => Name,
                       Args     => (1 => Args (1)),
                       Typ      => Base);
               end;
            end if;

         --  Otherwise, we are converting from a floting point or fixed
         --  point type.

         else
            raise Program_Error;
         end if;
      elsif Is_From_Hardcoded_Generic_Unit (Subp, Big_Reals)
        and then Name_String = BRN.Generic_To_Big_Real
      then
         pragma Assert (Args'Length = 1);

         declare
            From_Ty : constant Entity_Id :=
              Retysp (Etype (First_Formal (Subp)));
         begin
            if Is_Fixed_Point_Type (From_Ty) then
               T :=
                 New_Call
                   (Domain   => Domain,
                    Ada_Node => Ada_Node,
                    Name     => Real_Infix_Mult,
                    Args     =>
                      (1 =>
                         New_Call
                           (Domain   => Domain,
                            Ada_Node => Ada_Node,
                            Name     => M_Real_From_Int.From_Int,
                            Args     => (1 => Args (1))),
                       2 =>
                         New_Real_Constant
                           (Ada_Node => Ada_Node,
                            Value    => Small_Value (From_Ty))),
                    Typ      => Type_Of_Node (Etype (Subp)));
            else
               pragma Assert (Is_Floating_Point_Type (From_Ty));
               T :=
                 New_Call
                   (Domain   => Domain,
                    Ada_Node => Ada_Node,
                    Name     => MF_Floats (Base_Why_Type (From_Ty)).To_Real,
                    Args     => (1 => Args (1)),
                    Typ      => Type_Of_Node (Etype (Subp)));
            end if;
         end;

      elsif Is_From_Hardcoded_Unit (Subp, System_Storage_Elements) then
         pragma
           Assert
             (Name_String = SSEN.To_Integer
              or else Name_String = SSEN.To_Address);
         T :=
           Insert_Simple_Conversion
             (Ada_Node => Ada_Node,
              Domain   => Domain,
              Expr     => Args (1),
              To       => Type_Of_Node (Etype (Subp)));

      elsif Is_From_Hardcoded_Generic_Unit (Subp, Elementary_Functions) then
         declare
            Typ        : constant W_Type_Id := Base_Why_Type (Etype (Subp));
            MF         : M_Floating_Type renames MF_Floats (Typ);
            Nam        : constant String := Get_Name_String (Chars (Subp));
            Symb       : constant W_Identifier_Id :=
              (case Args'Length is
                 when 1      =>
                   (if Nam = EFN.Ada_Sqrt
                    then MF.Ada_Sqrt
                    elsif Nam = EFN.Log
                    then MF.Log
                    elsif Nam = EFN.Exp
                    then MF.Exp
                    elsif Nam = EFN.Sin
                    then MF.Sin
                    elsif Nam = EFN.Cos
                    then MF.Cos
                    elsif Nam = EFN.Tan
                    then MF.Tan
                    elsif Nam = EFN.Cot
                    then MF.Cot
                    elsif Nam = EFN.Arcsin
                    then MF.Arcsin
                    elsif Nam = EFN.Arccos
                    then MF.Arccos
                    elsif Nam = EFN.Sinh
                    then MF.Sinh
                    elsif Nam = EFN.Cosh
                    then MF.Cosh
                    elsif Nam = EFN.Tanh
                    then MF.Tanh
                    elsif Nam = EFN.Coth
                    then MF.Coth
                    elsif Nam = EFN.Arcsinh
                    then MF.Arcsinh
                    elsif Nam = EFN.Arccosh
                    then MF.Arccosh
                    elsif Nam = EFN.Arctanh
                    then MF.Arctanh
                    elsif Nam = EFN.Arccoth
                    then MF.Arccoth
                    else raise Program_Error),
                 when 2      =>
                   (if Chars (Subp) = Name_Op_Expon
                    then MF.Ada_Power
                    elsif Nam = EFN.Log
                    then MF.Log_Base
                    elsif Nam = EFN.Sin
                    then MF.Sin_2
                    elsif Nam = EFN.Cos
                    then MF.Cos_2
                    elsif Nam = EFN.Tan
                    then MF.Tan_2
                    elsif Nam = EFN.Cot
                    then MF.Cot_2
                    elsif Nam = EFN.Arcsin
                    then MF.Arcsin_2
                    elsif Nam = EFN.Arccos
                    then MF.Arccos_2
                    elsif Nam = EFN.Arctan
                    then MF.Arctan
                    elsif Nam = EFN.Arccot
                    then MF.Arccot
                    else raise Program_Error),
                 when 3      =>
                   (if Nam = EFN.Arctan
                    then MF.Arctan_2
                    elsif Nam = EFN.Arccot
                    then MF.Arccot_2
                    else raise Program_Error),
                 when others => raise Program_Error);
            Def_Domain : constant W_Identifier_Id :=
              (case Args'Length is
                 when 1      =>
                   (if Nam = EFN.Log
                    then MF.Log_Definition_Domain
                    elsif Nam = EFN.Cot
                    then MF.Cot_Definition_Domain
                    elsif Nam = EFN.Coth
                    then MF.Coth_Definition_Domain
                    elsif Nam = EFN.Arctanh
                    then MF.Arctanh_Definition_Domain
                    elsif Nam = EFN.Arccoth
                    then MF.Arccoth_Definition_Domain
                    elsif Nam = EFN.Arccosh
                    then MF.Arccosh_Definition_Domain
                    else Why_Empty),
                 when 2      =>
                   (if Chars (Subp) = Name_Op_Expon
                    then MF.Ada_Power_Definition_Domain
                    elsif Nam = EFN.Log
                    then MF.Log_Base_Definition_Domain
                    elsif Nam = EFN.Tan
                    then MF.Tan_2_Definition_Domain
                    elsif Nam = EFN.Cot
                    then MF.Cot_2_Definition_Domain
                    else Why_Empty),
                 when others => Why_Empty);
            --  Symbol for performing the check that arguments are in the
            --  domain of definition, when split from main symbol because
            --  there is also an overflow check.

            Reason : constant VC_Kind :=
              (if Present (Def_Domain)
                 or else Nam in EFN.Exp | EFN.Sinh | EFN.Cosh | EFN.Arcsinh
                 or else (Nam = EFN.Tan and then Args'Length = 1)
               then VC_Overflow_Check
               else VC_Precondition);
            --  When an elementary function has an associated Def_Domain check,
            --  what is left is necessarily an overflow check. This is also
            --  the case when the function is defined everywhere (over floats,
            --  tangent is not defined over all reals).
            --  Remaining symbols (square roots, reciprocal circular
            --  trigonometric function) may have a domain-of-definition check,
            --  but cannot overflow.

         begin
            if Domain = EW_Prog then
               return
                  Result : W_Expr_Id :=
                    +New_VC_Call
                       (Ada_Node => Ada_Node,
                        Name     => To_Program_Space (Symb),
                        Progs    => Args,
                        Reason   => Reason,
                        Typ      => MF.T)
               do
                  --  We emit a precondition check for the domain of definition
                  --  even though the actual Ada function symbol has no
                  --  precondition. Those are not in the Ada library because
                  --  the functions returns special infinity/Nan values instead
                  --  of failing, but SPARK does not handle such values.

                  if Present (Def_Domain) then
                     Prepend
                       (+New_VC_Call
                           (Ada_Node => Ada_Node,
                            Name     => Def_Domain,
                            Progs    => Args,
                            Reason   => VC_Precondition,
                            Typ      => EW_Unit_Type),
                        Result);
                  end if;
               end return;
            else
               return
                 New_Call
                   (Ada_Node => Ada_Node,
                    Domain   => Domain,
                    Name     => Symb,
                    Args     => Args,
                    Typ      => MF.T);
            end if;
         end;

      elsif Is_From_Hardcoded_Unit (Subp, Real_Time) then
         declare
            package RTN renames Real_Time_Names;
            Op      : W_Identifier_Id;
            Is_Time : constant Boolean :=
              Is_From_Hardcoded_Unit (Etype (Subp), Real_Time)
              and then
                Get_Name_String (Chars (Etype (Subp)))
                in RTN.Time | RTN.Time_Span;
            Res_Ty  : constant W_Type_Id :=
              (if Is_Time
               then Real_Time_Module.T
               else Base_Why_Type (Etype (Subp)));
         begin
            --  Conversions from integers. The of_int function takes a
            --  multiplying factor as two parameters for the numerator and
            --  denominator.

            if Get_Name_String (Chars (Subp))
               in RTN.Nanoseconds
                | RTN.Microseconds
                | RTN.Milliseconds
                | RTN.Seconds
                | RTN.Minutes
            then
               Op := Real_Time_Module.Of_Int;

               declare
                  N : Uint := Uint_1;
                  D : Uint := Uint_1;
               begin
                  if Get_Name_String (Chars (Subp)) = RTN.Nanoseconds then
                     D := UI_From_Int (1_000_000_000);
                  elsif Get_Name_String (Chars (Subp)) = RTN.Microseconds then
                     D := UI_From_Int (1_000_000);
                  elsif Get_Name_String (Chars (Subp)) = RTN.Milliseconds then
                     D := UI_From_Int (1_000);
                  elsif Get_Name_String (Chars (Subp)) = RTN.Minutes then
                     N := UI_From_Int (60);
                  end if;

                  T :=
                    New_Call
                      (Ada_Node => Ada_Node,
                       Domain   => Domain,
                       Name     => Op,
                       Args     =>
                         Args
                         & (New_Integer_Constant (Value => N),
                            New_Integer_Constant (Value => D)),
                       Typ      => Res_Ty);
               end;

            elsif Get_Name_String (Chars (Subp))
                  in RTN.To_Duration | RTN.To_Time_Span
            then
               if Get_Name_String (Chars (Subp)) = RTN.To_Duration then
                  Op := Real_Time_Module.To_Duration;
               else
                  Op := Real_Time_Module.Of_Duration;
               end if;

               T :=
                 New_Call
                   (Ada_Node => Ada_Node,
                    Domain   => Domain,
                    Name     => Op,
                    Args     => Args,
                    Typ      => Res_Ty);

            --  For Time_Of, generate time_of sc + ts. The rounding mode of
            --  time_of is not specified.

            elsif Get_Name_String (Chars (Subp)) = RTN.Time_Of then
               pragma Assert (Args'Length = 2);

               T :=
                 New_Call
                   (Ada_Node => Ada_Node,
                    Domain   => Domain,
                    Name     => Int_Infix_Add,
                    Args     =>
                      (1 =>
                         New_Call
                           (Ada_Node => Ada_Node,
                            Domain   => Domain,
                            Name     => Real_Time_Module.Time_Of,
                            Args     =>
                              (1 =>
                                 Insert_Simple_Conversion
                                   (Domain => Domain,
                                    Expr   => Args (1),
                                    To     => EW_Int_Type)),
                            Typ      => Res_Ty),
                       2 => Args (2)),
                    Typ      => Res_Ty);

            --  The effects of the operators on Time and Time_Span are as for
            --  the operators defined for integer types (RM-D-8).

            --  Comparison operators

            elsif Etype (Subp) = Standard_Boolean then
               pragma Assert (Args'Length = 2);

               if Domain = EW_Term then
                  if Chars (Subp) = Name_Op_Gt then
                     Op := M_Integer.Bool_Gt;
                  elsif Chars (Subp) = Name_Op_Lt then
                     Op := M_Integer.Bool_Lt;
                  elsif Chars (Subp) = Name_Op_Ge then
                     Op := M_Integer.Bool_Ge;
                  elsif Chars (Subp) = Name_Op_Le then
                     Op := M_Integer.Bool_Le;
                  else
                     raise Program_Error;
                  end if;
               else
                  if Chars (Subp) = Name_Op_Gt then
                     Op := Int_Infix_Gt;
                  elsif Chars (Subp) = Name_Op_Lt then
                     Op := Int_Infix_Lt;
                  elsif Chars (Subp) = Name_Op_Ge then
                     Op := Int_Infix_Ge;
                  elsif Chars (Subp) = Name_Op_Le then
                     Op := Int_Infix_Le;
                  else
                     raise Program_Error;
                  end if;
               end if;

               T :=
                 New_Comparison
                   (Symbol => Op,
                    Left   => Args (1),
                    Right  => Args (2),
                    Domain => Domain);

            --  Divison in the program domain

            elsif Domain = EW_Prog and then Chars (Subp) = Name_Op_Divide then
               T :=
                 New_Operator_Call
                   (Ada_Node => Ada_Node,
                    Domain   => Domain,
                    Name     => M_Int_Div.Div,
                    Args     => Args,
                    Reason   => VC_Division_Check,
                    Check    => True,
                    Typ      => Res_Ty);

            --  Other operators

            else
               if Chars (Subp) = Name_Op_Add then
                  Op := Int_Infix_Add;
               elsif Chars (Subp) = Name_Op_Subtract then
                  if Args'Length = 2 then
                     Op := Int_Infix_Subtr;
                  elsif Args'Length = 1 then
                     Op := Int_Unary_Minus;
                  else
                     raise Program_Error;
                  end if;
               elsif Chars (Subp) = Name_Op_Multiply then
                  Op := Int_Infix_Mult;
               elsif Chars (Subp) = Name_Op_Divide then
                  Op := New_Division (EW_Int_Type);
               elsif Chars (Subp) = Name_Op_Abs then
                  Op := New_Abs (EW_Int_Type);
               else
                  raise Program_Error;
               end if;

               T :=
                 New_Call
                   (Ada_Node => Ada_Node,
                    Domain   => Domain,
                    Name     => Op,
                    Args     => Args,
                    Typ      => Res_Ty);
            end if;

            --  If the result of the operation is Time or Time_Span, introduce
            --  a range check manually and set the appropriate type.

            if Is_Time then
               if Domain = EW_Prog then
                  declare
                     Tmp         : constant W_Expr_Id := New_Temp_For_Expr (T);
                     Range_Check : constant W_Identifier_Id :=
                       (if Get_Name_String (Chars (Etype (Subp)))
                          = Real_Time_Names.Time
                        then Real_Time_Module.In_Range_Time
                        elsif Get_Name_String (Chars (Etype (Subp)))
                          = Real_Time_Names.Time_Span
                        then Real_Time_Module.In_Range_Span
                        else raise Program_Error);
                  begin
                     T :=
                       +Sequence
                          (Left  =>
                             New_Located_Assert
                               (Ada_Node => Ada_Node,
                                Pred     =>
                                  New_Call
                                    (Name => Range_Check, Args => (1 => Tmp)),
                                Reason   => VC_Range_Check,
                                Kind     => EW_Assert),
                           Right => +Tmp);

                     T :=
                       Binding_For_Temp
                         (Domain => Domain, Tmp => Tmp, Context => T);
                  end;
               end if;

               T :=
                 New_Label
                   (Ada_Node => Ada_Node,
                    Domain   => Domain,
                    Labels   => Symbol_Sets.Empty_Set,
                    Def      => T,
                    Typ      => Type_Of_Node (Etype (Subp)));

            elsif Domain = EW_Prog and then Etype (Subp) /= Standard_Boolean
            then
               T :=
                 +Do_Range_Check
                    (Ada_Node   => Ada_Node,
                     Ty         => Etype (Subp),
                     W_Expr     => T,
                     Check_Kind => RCK_Range);
            end if;
         end;
      else
         raise Program_Error;
      end if;
      return T;
   end Transform_Hardcoded_Function_Call;

   ---------------------------------
   -- Transform_Hardcoded_Literal --
   ---------------------------------

   function Transform_Hardcoded_Literal
     (Call : Node_Id; Domain : EW_Domain) return W_Expr_Id
   is
      Subp      : constant Entity_Id := Get_Called_Entity_For_Proof (Call);
      Root_Type : constant W_Type_Id :=
        Type_Of_Node (Root_Retysp (Etype (Call)));
      Actual    : Node_Id := First_Actual (Call);

      function Transform_Quotient_Of_Strings
        (Num_String : String;
         Den_String : String;
         Num_Node   : Node_Id;
         Den_Node   : Node_Id) return W_Expr_Id;
      --  Transform a pair of strings representing integral
      --  numerator/denominator, or return Why_Empty
      --  if invalid representation.

      -----------------------------------
      -- Transform_Quotient_Of_Strings --
      -----------------------------------

      function Transform_Quotient_Of_Strings
        (Num_String : String;
         Den_String : String;
         Num_Node   : Node_Id;
         Den_Node   : Node_Id) return W_Expr_Id is
      begin
         declare
            --  Get the values of Strings as a Uint

            Num_Val : constant Uint := Uint_From_String (Num_String);
            Den_Val : constant Uint := Uint_From_String (Den_String);

            --  Return the appropriate real constant. Only emit a division
            --  check if Den_Val is 0.

            Subdomain : constant EW_Domain :=
              (if Domain = EW_Prog and then Den_Val /= Uint_0
               then EW_Pterm
               else Domain);
            W_Args    : constant W_Expr_Array :=
              (1 =>
                 New_Real_Constant
                   (Ada_Node => Num_Node, Value => UR_From_Uint (Num_Val)),
               2 =>
                 New_Real_Constant
                   (Ada_Node => Den_Node, Value => UR_From_Uint (Den_Val)));
            Name      : constant W_Identifier_Id :=
              (if Subdomain = EW_Prog then Real_Infix_Div else M_Real.Div);

            Result : constant W_Expr_Id :=
              New_Operator_Call
                (Ada_Node   => Call,
                 Domain     => Subdomain,
                 Name       => Name,
                 Fix_Name   => True,
                 Args       => W_Args,
                 Reason     => VC_Division_Check,
                 Check_Info => New_Check_Info (Divisor => Den_Node),
                 Check      => Subdomain = EW_Prog,
                 Typ        => EW_Real_Type);

         begin
            return
              New_Label
                (Ada_Node => Call,
                 Domain   => Domain,
                 Labels   => Symbol_Sets.Empty_Set,
                 Def      => Result,
                 Typ      => Root_Type);
         end;

      exception
         when Constraint_Error =>
            --  If the parameter is not a valid real value, or if its
            --  components exceed Long_Long_Integer, then default to
            --  imprecise translation.

            return Why_Empty;
      end Transform_Quotient_Of_Strings;

      --  Start of processing for Transform_Hardcoded_Literal

   begin
      --  Go over the actuals to check that their are all string literals

      while Present (Actual) loop
         if Nkind (Actual) /= N_String_Literal then
            return Why_Empty;
         end if;
         Actual := Next_Actual (Actual);
      end loop;

      --  Transformation of integer literals from Big_Integers

      if Is_From_Hardcoded_Unit (Subp, Big_Integers) then
         pragma Assert (Get_Name_String (Chars (Subp)) = BIN.From_String);

         declare
            String_Literal : constant Node_Id := First_Actual (Call);
            pragma
              Assert
                (Present (String_Literal)
                 and then No (Next_Actual (String_Literal)));
            Str_Value      : constant String_Id := Strval (String_Literal);
            Len            : constant Nat := String_Length (Str_Value);
            Value_String   : String (1 .. Natural (Len));
            UI_Val         : Uint;

         begin
            --  Fetch the value of the string literal

            String_To_Name_Buffer (Str_Value);
            Value_String := Name_Buffer (1 .. Natural (Len));

            --  Get its value as a Uint

            UI_Val := Uint_From_String (Value_String);

            --  Return the appropriate integer constant

            return
              New_Label
                (Ada_Node => String_Literal,
                 Domain   => Domain,
                 Labels   => Symbol_Sets.Empty_Set,
                 Def      =>
                   New_Integer_Constant
                     (Ada_Node => String_Literal, Value => UI_Val),
                 Typ      => Root_Type);

         exception
            when Constraint_Error =>
               --  If we did not manage to transform the literal to an integer,
               --  default to the imprecise translation.

               return Why_Empty;
         end;

      --  Transformation of real literals from Big_Reals

      elsif Is_From_Hardcoded_Unit (Subp, Big_Reals) then
         if Get_Name_String (Chars (Subp)) = BRN.From_String then
            declare
               function UI_From_Integer is new UI_From_Integral (Integer);

               String_Literal : constant Node_Id := First_Actual (Call);
               pragma
                 Assert
                   (Present (String_Literal)
                    and then No (Next_Actual (String_Literal)));
               Str_Value      : constant String_Id := Strval (String_Literal);
               Len            : constant Nat := String_Length (Str_Value);
               Arg            : String (1 .. Natural (Len));
               Frac           : Uint;
               Exp            : Uint := Uint_0;
               Pow            : Int := 0;
               Index          : Natural := 0;
               Last           : Natural := Arg'Last;
               Num            : Uint;
               Den            : Uint;
               Result         : W_Expr_Id;

            begin
               --  Fetch the value of the string literal

               String_To_Name_Buffer (Str_Value);
               Arg := Name_Buffer (Arg'Range);

               --  Parse the real value. The code is inspired from the
               --  implementation of Big_Reals.From_String.

               --  Search for:
               --    The last index before the dot, stored in Index,
               --    The last index before the exponent, stored in Last

               for J in reverse Arg'Range loop
                  if Arg (J) in 'e' | 'E' then
                     if Last /= Arg'Last then
                        raise Constraint_Error
                          with "multiple exponents specified";
                     end if;

                     Last := J - 1;
                     Pow := 0;
                     Exp :=
                       UI_From_Integer
                         (Integer'Value (Arg (J + 1 .. Arg'Last)));

                  elsif Arg (J) = '.' then
                     Index := J - 1;
                     exit;
                  else
                     Pow := Pow + 1;
                  end if;
               end loop;

               --  Pow is the number of digits after the dot

               pragma Assert (if Index /= 0 then Pow = Int (Last - Index - 1));

               --  Exp is the exponent if one was supplied 0 otherwise

               pragma
                 Assert
                   (if Last /= Arg'Last
                    then Exp = Uint_From_String (Arg (Last + 2 .. Arg'Last))
                    else Exp = Uint_0);

               if Index = 0 then
                  raise Constraint_Error with "invalid real value";
               end if;

               --  From <Int> . <Frac> E <Exp>,
               --  generate
               --     ((Int * 10 ** Pow +/- Frac) / 10 ** Pow) * 10 ** Exp

               Den := Uint_10 ** Pow;
               Num := Uint_From_String (Arg (Arg'First .. Index)) * Den;
               Frac := Uint_From_String (Arg (Index + 2 .. Last));

               if Num < Uint_0 then
                  Num := Num - Frac;
               else
                  Num := Num + Frac;
               end if;

               if Exp > Uint_0 then
                  Num := Num * Uint_10 ** Exp;
               elsif Exp < Uint_0 then
                  Den := Den * Uint_10 ** (-Exp);
               end if;

               --  Return the appropriate real constant. There is no possible
               --  division by zero, as Den cannot be 0.

               declare
                  Subdomain : constant EW_Domain :=
                    (if Domain = EW_Prog and then Den /= Uint_0
                     then EW_Pterm
                     else Domain);
                  W_Args    : constant W_Expr_Array :=
                    (1 =>
                       New_Real_Constant
                         (Ada_Node => String_Literal,
                          Value    => UR_From_Uint (Num)),
                     2 =>
                       New_Real_Constant
                         (Ada_Node => String_Literal,
                          Value    => UR_From_Uint (Den)));
                  Name      : constant W_Identifier_Id :=
                    (if Subdomain = EW_Prog
                     then Real_Infix_Div
                     else M_Real.Div);
               begin
                  Result :=
                    New_Operator_Call
                      (Ada_Node => Call,
                       Domain   => Subdomain,
                       Name     => Name,
                       Fix_Name => True,
                       Args     => W_Args,
                       Reason   => VC_Division_Check,
                       Check    => False,
                       Typ      => EW_Real_Type);
               end;

               return
                 New_Label
                   (Ada_Node => String_Literal,
                    Domain   => Domain,
                    Labels   => Symbol_Sets.Empty_Set,
                    Def      => Result,
                    Typ      => Root_Type);

            exception
               when Constraint_Error =>
                  --  If the parameter is not a valid real value, or if its
                  --  components exceed Long_Long_Integer, then default to
                  --  imprecise translation.

                  return Why_Empty;
            end;

         elsif Get_Name_String (Chars (Subp)) = BRN.From_Universal_Image then
            declare
               Num_Literal : constant Node_Id := First_Actual (Call);
               pragma Assert (Present (Num_Literal));
               Den_Literal : constant Node_Id := Next_Actual (Num_Literal);
               pragma
                 Assert
                   (Present (Den_Literal)
                    and then No (Next_Actual (Den_Literal)));
               Num_Str_Id  : constant String_Id := Strval (Num_Literal);
               Den_Str_Id  : constant String_Id := Strval (Den_Literal);
               Num_Len     : constant Natural :=
                 Natural (String_Length (Num_Str_Id));
               Den_Len     : constant Natural :=
                 Natural (String_Length (Den_Str_Id));
               Num_String  : String (1 .. Num_Len);
               Den_String  : String (1 .. Den_Len);
            begin
               --  Fetch the value of the string literals

               String_To_Name_Buffer (Num_Str_Id);
               Num_String := Name_Buffer (1 .. Num_Len);
               String_To_Name_Buffer (Den_Str_Id);
               Den_String := Name_Buffer (1 .. Den_Len);
               return
                 Transform_Quotient_Of_Strings
                   (Num_String, Den_String, Num_Literal, Den_Literal);
            end;
         elsif Get_Name_String (Chars (Subp)) = BRN.From_Quotient_String then
            declare
               Quot_Literal : constant Node_Id := First_Actual (Call);
               pragma
                 Assert
                   (Present (Quot_Literal)
                    and then No (Next_Actual (Quot_Literal)));
               Quot_Str_Id  : constant String_Id := Strval (Quot_Literal);
               Quot_Len     : constant Natural :=
                 Natural (String_Length (Quot_Str_Id));
               Quot_String  : String (1 .. Quot_Len);
               J            : Natural := 1;
            begin
               --  Fetch the value of the quotient literal

               String_To_Name_Buffer (Quot_Str_Id);
               Quot_String := Name_Buffer (1 .. Quot_Len);

               --  Find the quotient symbol and split the quotient string

               loop
                  if J > Quot_Len then
                     --  Not present, resort to default imprecise translation

                     return Why_Empty;
                  end if;
                  exit when Quot_String (J) = '/';
                  J := J + 1;
               end loop;

               return
                 Transform_Quotient_Of_Strings
                   (Quot_String (1 .. J - 1),
                    Quot_String (J + 1 .. Quot_Len),
                    Quot_Literal,
                    Quot_Literal);
            end;
         else
            raise Program_Error;
         end if;
      else
         raise Program_Error;
      end if;
   end Transform_Hardcoded_Literal;

   -----------------------------------
   -- Transform_Hardcoded_Operation --
   -----------------------------------

   function Transform_Hardcoded_Operation
     (Op                  : N_Binary_Op;
      Lty, Rty, Expr_Type : Type_Kind_Id;
      LT, RT              : W_Expr_Id;
      Domain              : EW_Domain;
      Ada_Node            : Node_Id) return W_Expr_Id
   is
      T   : W_Expr_Id;
      RTT : constant W_Expr_Id := New_Temp_For_Expr (RT, Domain = EW_Prog);
   begin
      pragma Assert (Op = N_Op_Mod);
      pragma Assert (Is_System_Address (Lty) and then Has_Stoele_Offset (Rty));
      T :=
        New_Binary_Op_Expr
          (Op          => Op,
           Left        => LT,
           Right       => RTT,
           Left_Type   => Lty,
           Right_Type  => Rty,
           Return_Type => Expr_Type,
           Domain      => Domain,
           Ada_Node    => Ada_Node);
      if Domain = EW_Prog then
         declare
            Ty    : constant W_Type_Id := Base_Why_Type (Retysp (Rty));
            Check : W_Pred_Id;
         begin
            Check :=
              New_VC_Pred
                (Ada_Node,
                 New_Comparison
                   (Transform_Compare_Op (N_Op_Gt, Ty, Domain),
                    +Insert_Simple_Conversion
                       (Ada_Node, EW_Pred, RTT, EW_Int_Type),
                    New_Integer_Constant (Value => Uint_0)),
                 VC_Precondition);
            T :=
              +Sequence
                 (New_Assert
                    (Ada_Node    => Ada_Node,
                     Assert_Kind => EW_Check,
                     Pred        => Check),
                  +T);
         end;
      end if;
      T := Binding_For_Temp (Empty, Domain, RTT, T);
      return T;
   end Transform_Hardcoded_Operation;

   ----------------------------------------
   -- Transform_Hardcoded_Procedure_Call --
   ----------------------------------------

   function Transform_Hardcoded_Procedure_Call
     (Subp : Entity_Id; Args : W_Expr_Array; Ada_Node : Node_Id)
      return W_Prog_Id is
   begin
      if Is_From_Hardcoded_Unit (Subp, Real_Time) then
         pragma
           Assert (Get_Name_String (Chars (Subp)) = Real_Time_Names.Split);
         pragma Assert (Args'Length = 3);

         --  Generate:
         --
         --    let tmp_t = t in
         --      havoc sc;
         --      havoc ts;
         --      assume { split tmp_t !sc !ts };
         --      ignore (range_check_ sc)

         declare
            T_Arg    : constant W_Expr_Id := New_Temp_For_Expr (Args (1));
            Sc_Typ   : constant Entity_Id :=
              Etype (Next_Formal (First_Formal (Subp)));
            Sc_Id    : constant W_Identifier_Id := +Args (2);
            Sc_Deref : constant W_Expr_Id :=
              New_Deref (Right => Sc_Id, Typ => Get_Typ (Sc_Id));
            Ts_Id    : constant W_Identifier_Id := +Args (3);
            Ts_Deref : constant W_Expr_Id :=
              New_Deref (Right => Ts_Id, Typ => Get_Typ (Ts_Id));

         begin
            return
              Binding_For_Temp
                (Ada_Node => Ada_Node,
                 Tmp      => +T_Arg,
                 Context  =>
                   Sequence
                     ((1 => New_Havoc_Call (Sc_Id),
                       2 => New_Havoc_Call (Ts_Id),
                       3 =>
                         New_Assume_Statement
                           (Pred =>
                              New_Call
                                (Name => Real_Time_Module.Split,
                                 Args =>
                                   (1 => T_Arg,
                                    2 => Sc_Deref,
                                    3 => Ts_Deref))),
                       4 =>
                         New_Ignore
                           (Prog =>
                              Do_Range_Check
                                (Ada_Node   => Ada_Node,
                                 Ty         => Sc_Typ,
                                 W_Expr     => Sc_Deref,
                                 Check_Kind => RCK_Range)))));
         end;
      else
         raise Program_Error;
      end if;
   end Transform_Hardcoded_Procedure_Call;

   ----------------------
   -- Uint_From_String --
   ----------------------

   function Uint_From_String (Str_Value : String) return Uint is

      function UI_From_Long_Long_Long_Integer is new
        UI_From_Integral (Long_Long_Long_Integer);

      Def    : Long_Long_Long_Integer;
      UI_Val : Uint;

   begin
      --  Try to get the value of Str_Value as a long long long integer

      Def := Long_Long_Long_Integer'Value (Str_Value);

      --  Transform Def into a Uint

      UI_Val := UI_From_Long_Long_Long_Integer (Def);

      return UI_Val;

   exception
      when Constraint_Error =>

         --  Otherwise, try the slow path

         declare
            Neg    : Boolean := False;
            J      : Natural := Str_Value'First;
            Result : Uint := Uint_0;

         begin
            --  Scan past leading blanks

            while J <= Str_Value'Last and then Str_Value (J) = ' ' loop
               J := J + 1;
            end loop;

            if J > Str_Value'Last then
               raise;
            end if;

            --  Scan and store negative sign if found

            if Str_Value (J) = '-' then
               Neg := True;
               J := J + 1;
            end if;

            --  Scan decimal value. If something which is not between '0' and
            --  '9' or '_' is found ('#' or 'E') we don't support it yet.

            while J <= Str_Value'Last loop
               if Str_Value (J) in '0' .. '9' then
                  Result :=
                    UI_Add
                      (UI_Mul (Result, Uint_10),
                       (case Str_Value (J) is
                          when '0'    => Uint_0,
                          when '1'    => Uint_1,
                          when '2'    => Uint_2,
                          when '3'    => Uint_3,
                          when '4'    => Uint_4,
                          when '5'    => Uint_5,
                          when '6'    => Uint_6,
                          when '7'    => Uint_7,
                          when '8'    => Uint_8,
                          when '9'    => Uint_9,
                          when others => raise Program_Error));
               elsif Str_Value (J) = '_' then
                  if J = Str_Value'Last or else Str_Value (J + 1) = '_' then
                     raise;
                  end if;
               else
                  raise;
               end if;

               J := J + 1;
            end loop;

            if Neg then
               return UI_Negate (Result);
            else
               return Result;
            end if;
         end;
   end Uint_From_String;

end Why.Gen.Hardcoded;
