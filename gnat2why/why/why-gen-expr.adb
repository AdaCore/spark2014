------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                          W H Y - G E N - E X P R                         --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                       Copyright (C) 2010-2015, AdaCore                   --
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

with Ada.Strings.Unbounded;   use Ada.Strings.Unbounded;
with Ada.Text_IO;

with Aspects;                 use Aspects;
with Atree;                   use Atree;
with Checks;                  use Checks;
with Einfo;                   use Einfo;
with Errout;                  use Errout;
with Nlists;                  use Nlists;
with Sem_Eval;                use Sem_Eval;
with Sem_Util;                use Sem_Util;
with Sinfo;                   use Sinfo;
with Sinput;                  use Sinput;
with Stand;                   use Stand;
with String_Utils;            use String_Utils;
with Uintp;                   use Uintp;
with Urealp;                  use Urealp;

with SPARK_Definition;        use SPARK_Definition;
with SPARK_Util;              use SPARK_Util;

with Why.Atree.Accessors;     use Why.Atree.Accessors;
with Why.Atree.Tables;        use Why.Atree.Tables;
with Why.Atree.Modules;       use Why.Atree.Modules;
with Why.Conversions;         use Why.Conversions;
with Why.Gen.Arrays;          use Why.Gen.Arrays;
with Why.Gen.Names;           use Why.Gen.Names;
with Why.Gen.Preds;           use Why.Gen.Preds;
with Why.Gen.Progs;           use Why.Gen.Progs;
with Why.Gen.Records;         use Why.Gen.Records;
with Why.Inter;               use Why.Inter;

with Gnat2Why.Error_Messages; use Gnat2Why.Error_Messages;
with Gnat2Why.Expr;           use Gnat2Why.Expr;
with Gnat2Why.Subprograms;    use Gnat2Why.Subprograms;

with Ada.Strings.Fixed;

package body Why.Gen.Expr is

   Pretty_Ada_Tag : constant String := "GP_Pretty_Ada";

   function Insert_Single_Conversion
     (Ada_Node : Node_Id;
      Domain   : EW_Domain;
      To       : W_Type_Id;
      Expr     : W_Expr_Id) return W_Expr_Id;
   --  Assuming that there is at most one step between To and From in the
   --  type hierarchy (i.e. that it exists a conversion from From
   --  to To; a counterexample would be two abstract types whose base
   --  types differ), insert the corresponding conversion.

   function Insert_Single_Conversion
     (Ada_Node : Node_Id;
      Domain   : EW_Domain;
      From     : W_Type_Id;
      To       : W_Type_Id;
      Expr     : W_Expr_Id) return W_Expr_Id;
   --  Same as above, except the From type is explicitly given. This is useful
   --  for conversions with fixed-point types, as the base type EW_Fixed does
   --  not allow retrieving the name of the appropriate conversion function,
   --  only the abstract fixed-point type allows it.

   Temp_Names_Map : Why_Node_Maps.Map := Why_Node_Maps.Empty_Map;

   ----------------------
   -- Binding_For_Temp --
   ----------------------

   function Binding_For_Temp
     (Ada_Node : Node_Id := Empty;
      Domain   : EW_Domain;
      Tmp      : W_Expr_Id;
      Context  : W_Expr_Id)
     return W_Expr_Id
   is
      use Why_Node_Maps;
      C : Cursor := Temp_Names_Map.Find (+Tmp);
   begin

      --  if Tmp is in the map, we really introduced a temp variable and need
      --  to build a binding now.

      if Has_Element (C) then
         declare
            E : constant W_Expr_Id := +Element (C);
         begin

            --  we delete the entry, so that the map doesn't grow too much.

            Temp_Names_Map.Delete (C);

            return
              New_Typed_Binding
                (Ada_Node => Ada_Node,
                 Domain   => Domain,
                 Name     => +Tmp,
                 Def      => E,
                 Context  => Context);
         end;
      else

         --  Otherwise Tmp is not a temp associated with an expression.
         --  Presumably, no temp variable was actually created for it during
         --  a call of New_Temp_For_Expr. We just return the context.

         return Context;
      end if;
   end Binding_For_Temp;

   -------------------
   -- Cur_Subp_Sloc --
   -------------------

   function Cur_Subp_Sloc return Name_Id is
   begin
      return NID (Subp_Location (Current_Subp));
   end Cur_Subp_Sloc;

   --------------
   -- Get_Type --
   --------------

   function Get_Type (E : W_Expr_Id) return W_Type_Id is
   begin
      case Get_Kind (+E) is
         when W_Integer_Constant =>
            return EW_Int_Type;

         when W_Fixed_Constant =>
            return EW_Fixed_Type;

         when W_Real_Constant =>
            return EW_Real_Type;

         when W_Literal =>
            return EW_Bool_Type;

         when W_Void
            | W_While_Loop
            | W_Assignment
            | W_Assert =>
            return EW_Unit_Type;

         when W_Relation
            | W_Connection
            | W_Not
            | W_Universal_Quantif
            | W_Existential_Quantif =>
            return EW_Bool_Type;

         when W_Binary_Op =>
            return Why_Types (Get_Op_Type (W_Binary_Op_Id (E)));

         when W_Unary_Op =>
            return Why_Types (Get_Op_Type (W_Unary_Op_Id (E)));

         when W_Identifier =>
            return Get_Typ (W_Identifier_Id (E));

         when W_Tagged =>
            return Get_Typ (W_Tagged_Id (E));

         when W_Call =>
            return Get_Typ (W_Call_Id (E));

         when W_Binding =>
            return Get_Typ (W_Binding_Id (E));

         when W_Elsif =>
            return Get_Typ (W_Elsif_Id (E));

         when W_Conditional =>
            return Get_Typ (W_Conditional_Id (E));

         when W_Deref =>
            return Get_Typ (W_Deref_Id (E));

         when W_Record_Access =>
            return Get_Typ (W_Record_Access_Id (E));

         when W_Record_Update =>
            return Get_Typ (W_Record_Update_Id (E));

         when W_Record_Aggregate =>
            return Get_Typ (W_Record_Aggregate_Id (E));

         when W_Binding_Ref =>
            return Get_Typ (W_Binding_Ref_Id (E));

         when W_Any_Expr =>
            return Get_Return_Type (W_Any_Expr_Id (E));

         when W_Abstract_Expr =>
            return Get_Typ (W_Abstract_Expr_Id (E));

         when W_Try_Block =>
            return Get_Typ (W_Try_Block_Id (E));

         when W_Raise =>
            return Get_Typ (W_Raise_Id (E));

         when W_Label =>
            return Get_Typ (W_Label_Id (E));

         --  ??? The following nodes should get their own Type field at some
         --  point, right now we use recursion.

         when W_Statement_Sequence =>
            declare
               use Why_Node_Lists;
               L : constant List :=
                 Get_List (+Get_Statements (W_Statement_Sequence_Id (E)));
            begin
               return Get_Type (+Last_Element (L));
            end;

         when others =>
            raise Program_Error;
      end case;

   end Get_Type;

   -----------------------------
   -- Insert_Array_Conversion --
   -----------------------------

   function Insert_Array_Conversion
     (Domain     : EW_Domain;
      Ada_Node   : Node_Id := Empty;
      Expr       : W_Expr_Id;
      To         : W_Type_Id;
      Need_Check : Boolean := False;
      Force_No_Slide : Boolean := False)
      return W_Expr_Id
   is
      From      : constant W_Type_Id := Get_Type (Expr);
      To_Ent    : constant Entity_Id := Get_Ada_Node (+To);
      From_Ent  : constant Entity_Id := Get_Ada_Node (+From);
      Dim       : constant Positive := Positive (Number_Dimensions (To_Ent));

      function Needs_Slide (From_Ent, To_Ent : Entity_Id) return Boolean;
      --  Check whether a conversion between those types requires sliding.

      function Insert_Length_Check
        (Expr   : W_Expr_Id;
         To_Ent : Entity_Id) return W_Prog_Id;

      function Insert_Array_Range_Check
        (Expr   : W_Expr_Id;
         To_Ent : Entity_Id) return W_Prog_Id;

      ------------------------------
      -- Insert_Array_Range_Check --
      ------------------------------

      function Insert_Array_Range_Check
        (Expr   : W_Expr_Id;
         To_Ent : Entity_Id) return W_Prog_Id
      is
         Check   : W_Pred_Id;
         Args    : W_Expr_Array (1 .. 2 * Dim);
         Arg_Ind : Positive := 1;
      begin

         if not Is_Static_Array_Type (To_Ent) then

            --  For dynamic types, use dynamic_property instead of range_check

            Check := +New_Dynamic_Property
              (Domain => EW_Prog,
               Ty     => To_Ent,
               Expr   => Expr);

         else

            for I in 1 .. Dim loop
               Add_Attr_Arg
                 (EW_Prog, Args, Expr, Attribute_First, I, Arg_Ind);
               Add_Attr_Arg
                 (EW_Prog, Args, Expr, Attribute_Last, I, Arg_Ind);
            end loop;
            Check :=
              New_Call (Name   =>
                          Prefix (Ada_Node => To_Ent,
                                  M        => E_Module (To_Ent),
                                  N        => "range_check"),
                        Args   => Args,
                        Typ    => EW_Abstract (To_Ent));
         end if;

         return New_Located_Assert (Ada_Node,
                                    Check,
                                    VC_Range_Check,
                                    EW_Assert);
      end Insert_Array_Range_Check;

      -------------------------
      -- Insert_Length_Check --
      -------------------------

      function Insert_Length_Check
        (Expr   : W_Expr_Id;
         To_Ent : Entity_Id) return W_Prog_Id
      is
         Check : W_Pred_Id := True_Pred;
      begin
         for I in 1 .. Dim loop
            declare
               Input_Length    : constant W_Expr_Id :=
                 Build_Length_Expr (Domain, Expr, I);
               Expected_Length : constant W_Expr_Id :=
                 Build_Length_Expr (Domain, To_Ent, I);
            begin
               Check :=
                 +New_And_Then_Expr
                   (Domain => EW_Pred,
                    Left   => +Check,
                    Right  =>
                      New_Relation
                        (Domain  => Domain,
                         Op_Type => EW_Int,
                         Op      => EW_Eq,
                         Left    => +Input_Length,
                         Right   => +Expected_Length));
            end;
         end loop;
         return
           New_Located_Assert (Ada_Node, Check, VC_Length_Check, EW_Assert);
      end Insert_Length_Check;

      -----------------
      -- Needs_Slide --
      -----------------

      function Needs_Slide (From_Ent, To_Ent : Entity_Id) return Boolean is
      begin
         --  Sliding is needed when we convert to a constrained type and the
         --  'First of the From type is not known to be equal to the 'First
         --  of the "To" type.

         --  Sliding is only necessary when converting to a constrained array

         if not Is_Constrained (To_Ent) then
            return False;
         end if;

         --  When the "To" is constrained, sliding is always necessary when
         --  converting from an unconstrained array

         if not Is_Constrained (From_Ent) then
            return True;
         end if;

         --  Here we have two constrained types, and we check if the 'First (I)
         --  of both types differ for some dimension I

         for I in 1 .. Dim loop
            declare
               Low_From : constant Node_Id :=
                 Get_Low_Bound (Nth_Index_Type (From_Ent, Dim));
               Low_To : constant Node_Id :=
                 Get_Low_Bound (Nth_Index_Type (To_Ent, Dim));
            begin
               if not Is_Static_Expression (Low_From) or else
                 not Is_Static_Expression (Low_To) or else
                 Expr_Value (Low_From) /= Expr_Value (Low_To)
               then
                  return True;
               end if;
            end;
         end loop;

         --  We statically know that the "first" are actually equal, no sliding
         --  needed

         return False;
      end Needs_Slide;

      Sliding     : constant Boolean :=
        not Force_No_Slide and then Needs_Slide (From_Ent, To_Ent);
      Arr_Expr    : W_Expr_Id;
      T           : W_Expr_Id;
      Arg_Ind     : Positive := 1;

      --  Beginning of processing for Insert_Array_Conversion

   begin

      if To_Ent = From_Ent then

         --  In the case of unconstrained arrays, the Ada entity may be equal,
         --  but in Why we have to convert from the split representation to the
         --  unique representation. This is checked here.

         if not Is_Static_Array_Type (To_Ent) then
            if Get_Base_Type (From) = EW_Split and then
              Get_Base_Type (To) = EW_Abstract
            then
               return Array_Convert_From_Base (Domain, Expr);
            elsif Get_Base_Type (From) = EW_Abstract and then
              Get_Base_Type (To) = EW_Split
            then
               return Array_Convert_To_Base (Domain, Expr);
            else
               return Expr;
            end if;

         else

            --  No range check needed

            return Expr;
         end if;
      end if;

      Arr_Expr :=
        New_Temp_For_Expr
          (Expr,
           Need_Temp => Sliding or else not Is_Static_Array_Type (From_Ent));

      if Is_Static_Array_Type (To_Ent) or else
        Get_Base_Type (To) = EW_Split
      then
         if Sliding then
            declare
               Args    : W_Expr_Array (1 .. 1 + 2 * Dim);
            begin
               Add_Map_Arg (Domain, Args, Arr_Expr, Arg_Ind);
               for I in 1 .. Dim loop
                  Add_Attr_Arg
                    (Domain, Args, Arr_Expr,
                     Attribute_First, Dim, Arg_Ind);
                  Add_Attr_Arg
                    (Domain, Args, To_Ent,
                     Attribute_First, Dim, Arg_Ind);
               end loop;
               T := New_Call
                 (Domain => Domain,
                  Name   =>
                    Prefix (M => Array_Modules (Dim),
                            N => "slide"),
                  Args   => Args,
                  Typ    => To);
            end;
         elsif not Is_Static_Array_Type (From_Ent) and then
           Get_Base_Type (From) /= EW_Split
         then
            T :=
              New_Call
                (Domain => Domain,
                 Name   =>
                   Prefix (Ada_Node => From_Ent,
                           M        => E_Module (From_Ent),
                           W        => WNE_To_Array),
                 Args => (1 => Arr_Expr),
                 Typ  => To);

         --  No actual why call or conversion is inserted here, but we still
         --  need to change the type of the Why AST node. We do that by adding
         --  a dummy node

         else
            T := New_Label (Labels => Name_Id_Sets.Empty_Set,
                            Def    => Arr_Expr,
                            Domain => Domain,
                            Typ    => To);
         end if;
      else
         declare
            Args     : W_Expr_Array (1 .. 2 * Dim + 1);
            Arg_Ind  : Positive := 1;
         begin
            Add_Array_Arg (Domain, Args, Arr_Expr, Arg_Ind);
            T :=
              New_Call
                (Domain => Domain,
                 Name   =>
                   Prefix (Ada_Node => To_Ent,
                           M        => E_Module (To_Ent),
                           W        => WNE_Of_Array),
                 Args => Args,
                 Typ  => To);
         end;
      end if;

      if Domain = EW_Prog and Need_Check then
         declare
            Check_Type : constant Entity_Id := Get_Ada_Node (+To);
         begin
            if Is_Constrained (Check_Type) then
               T := +Sequence
                 (Insert_Length_Check (Arr_Expr, Check_Type),
                  +T);
            else
               T := +Sequence
                 (Insert_Array_Range_Check (Arr_Expr, Check_Type),
                 +T);
            end if;
         end;
      end if;

      T := Binding_For_Temp (Domain  => Domain,
                             Tmp     => Arr_Expr,
                             Context => T);
      return T;
   end Insert_Array_Conversion;

   -------------------------------
   -- Insert_Checked_Conversion --
   -------------------------------

   function Insert_Checked_Conversion
     (Ada_Node : Node_Id;
      Ada_Type : Entity_Id;
      Domain   : EW_Domain;
      Expr     : W_Expr_Id;
      To       : W_Type_Id) return W_Expr_Id
   is
      --  When converting between Ada types, detect cases where a check is not
      --  needed.

      From : constant W_Type_Id := Get_Type (Expr);
      Check_Needed : constant Boolean :=
        (if Get_Base_Type (From) in EW_Abstract | EW_Split
              and
            Get_Base_Type (To) in EW_Abstract | EW_Split
         then
            Check_Needed_On_Conversion (From => Get_Ada_Node (+From),
                                        To   => Get_Ada_Node (+To))
         else
            True);

      T : W_Expr_Id := Expr;

   begin

      if Is_Private_Conversion (From, To) then
         --  No conversion is needed between private types, but a discriminant
         --  check may be needed.

         T := Insert_Private_Conversion (Domain     => Domain,
                                         Ada_Node   => Ada_Node,
                                         Expr       => T,
                                         To         => To,
                                         Need_Check => Check_Needed);

      elsif Is_Record_Conversion (From, To) then
         --  Conversion between record types need to go through their common
         --  root record type. A discriminant check may be needed. Currently
         --  perform it on all discriminant record types, as the flag
         --  Do_Discriminant_Check is not set appropriately by the frontend on
         --  type conversions.

         T := Insert_Record_Conversion (Domain     => Domain,
                                        Ada_Node   => Ada_Node,
                                        Expr       => T,
                                        To         => To,
                                        Need_Check => Check_Needed);

      elsif Is_Array_Conversion (From, To) then
         --  The flag Do_Length_Check is not set consistently in the
         --  frontend, so check every array conversion.

         T := Insert_Array_Conversion (Domain     => Domain,
                                       Ada_Node   => Ada_Node,
                                       Expr       => T,
                                       To         => To,
                                       Need_Check => Check_Needed);

      --  Conversion between scalar types

      else
         declare
            --  Node whose Etype gives the bounds for a range check, if not
            --  Empty. This node is directly Expr when Do_Range_Check is
            --  set, or the expression of a type conversion whose flag
            --  Do_Overflow_Check is set. (See description of these flags
            --  in sinfo.ads for details.)

            --  We can't rely on check flags for subtype predicates, so force
            --  check_node in that case

            Do_Check : constant Boolean :=
              (if Domain = EW_Prog and Check_Needed then
                 (if Do_Range_Check (Ada_Node) then
                    True
                  elsif Nkind (Parent (Ada_Node)) = N_Type_Conversion
                    and then Do_Overflow_Check (Parent (Ada_Node))
                  then
                     True
                  else Get_Base_Type (To) = EW_Abstract
                    and then Has_Predicates (Get_Ada_Node (+To)))
               else False);

            --  When converting to a floating-point, from either a discrete
            --  type or another real type, rounding should be applied on the
            --  value of type real. Round_Func is the appropriate rounding
            --  function for the type.

            Round_Func : constant W_Identifier_Id :=
              (if Nkind (Ada_Node) = N_Type_Conversion
                 and then Ekind (Ada_Type) in Float_Kind
               then
                  Float_Round_Name (Ada_Type)
               else Why_Empty);

         begin
            T := Insert_Scalar_Conversion (Domain      => Domain,
                                           Ada_Node    => Ada_Node,
                                           Expr        => T,
                                           To          => To,
                                           Round_Func  => Round_Func,
                                           Do_Check    => Do_Check);
         end;
      end if;

      return T;
   end Insert_Checked_Conversion;

   -------------------------------
   -- Insert_Private_Conversion --
   -------------------------------

   function Insert_Private_Conversion
     (Ada_Node   : Node_Id;
      Domain     : EW_Domain;
      Expr       : W_Expr_Id;
      To         : W_Type_Id;
      Need_Check : Boolean := False) return W_Expr_Id
   is
      From       : constant W_Type_Id := Get_Type (Expr);

      L : constant Node_Id := Get_Ada_Node (+From);
      R : constant Node_Id := Get_Ada_Node (+To);

      pragma Assert (Get_First_Ancestor_In_SPARK (L) =
                       Get_First_Ancestor_In_SPARK (R));

   begin
      --  When From = To and no check needs to be inserted, do nothing

      if not Need_Check
        or else To = From
        or else not Has_Discriminants (L)
        or else Get_First_Ancestor_In_SPARK (L) = R
      then
         return Expr;
      end if;

      --  No need for a conversion as private types have in fact the same type.
      --  We only output the checks.

      if Domain = EW_Prog and Need_Check then
         return +Insert_Subtype_Discriminant_Check (Ada_Node, R, +Expr);
      end if;

      return Expr;
   end Insert_Private_Conversion;

   ------------------------------
   -- Insert_Record_Conversion --
   ------------------------------

   function Insert_Record_Conversion
     (Ada_Node   : Node_Id;
      Domain     : EW_Domain;
      Expr       : W_Expr_Id;
      To         : W_Type_Id;
      Need_Check : Boolean := False) return W_Expr_Id
   is
      From       : constant W_Type_Id := Get_Type (Expr);
      --  Current result expression
      Result : W_Expr_Id := Expr;

      L : constant Node_Id := Get_Ada_Node (+From);
      R : constant Node_Id := Get_Ada_Node (+To);
      pragma Assert (Root_Record_Type (L) = Root_Record_Type (R));

      Base : constant W_Type_Id := EW_Abstract (Root_Record_Type (L));

   begin
      --  When From = To and no check needs to be inserted, do nothing

      if Eq_Base (To, From) and not Need_Check then
         return Expr;
      end if;

      --  1. Convert From -> Base

      Result := Insert_Single_Conversion (Domain   => Domain,
                                          Ada_Node => Ada_Node,
                                          To       => Base,
                                          Expr     => Result);

      --  2. Possibly perform the discriminant check

      if Domain = EW_Prog and Need_Check then
         declare
            Check_Entity : constant Entity_Id := Get_Ada_Node (+To);
         begin
            Result := +Insert_Subtype_Discriminant_Check (Ada_Node,
                                                          Check_Entity,
                                                          +Result);
         end;
      end if;

      --  3. Convert Base -> To

      Result := Insert_Single_Conversion (Domain   => Domain,
                                          Ada_Node => Ada_Node,
                                          To       => To,
                                          Expr     => Result);

      return Result;
   end Insert_Record_Conversion;

   --------------------
   -- Do_Index_Check --
   --------------------

   function Do_Index_Check
     (Ada_Node   : Node_Id;
      Arr_Expr   : W_Expr_Id;
      W_Expr     : W_Expr_Id;
      Dim        : Positive) return W_Prog_Id
   is
      Tmp        : constant W_Expr_Id :=
        New_Temp_For_Expr (W_Expr);
      First_Expr : constant W_Expr_Id :=
        Insert_Simple_Conversion (Domain => EW_Term,
                                  Expr   => Get_Array_Attr
                                    (Domain => EW_Term,
                                     Expr   => Arr_Expr,
                                     Attr   => Attribute_First,
                                     Dim    => Dim),
                                  To     => EW_Int_Type);
      Last_Expr  : constant W_Expr_Id :=
        Insert_Simple_Conversion (Domain => EW_Term,
                                  Expr   => Get_Array_Attr
                                    (Domain => EW_Term,
                                     Expr   => Arr_Expr,
                                     Attr   => Attribute_Last,
                                     Dim    => Dim),
                                  To     => EW_Int_Type);
      T : W_Prog_Id;
   begin
      T := New_Located_Assert (Ada_Node => Ada_Node,
                               Reason   => VC_Index_Check,
                               Pred     => +New_Range_Expr
                                 (Domain => EW_Pred,
                                  Low    => First_Expr,
                                  High   => Last_Expr,
                                  Expr   => Tmp),
                               Kind     => EW_Assert);

      return +Binding_For_Temp (Domain => EW_Prog,
                                Tmp    => Tmp,
                                Context => +Sequence (T, +Tmp));
   end Do_Index_Check;

   --------------------
   -- Do_Range_Check --
   --------------------

   function Do_Range_Check
     (Ada_Node   : Node_Id;
      Ty         : Entity_Id;
      W_Expr     : W_Expr_Id;
      Check_Kind : Range_Check_Kind) return W_Prog_Id is
   begin
      if (not Is_Static_Subtype (Ty) and then Is_Discrete_Type (Ty))
        or else Type_Is_Modeled_As_Int_Or_Real (Ty)
      then
         declare
            Expr : constant W_Expr_Id := New_Temp_For_Expr (W_Expr);
            M : constant W_Module_Id :=
              (if Is_Standard_Boolean_Type (Ty) then Boolean_Module
               else E_Module (Ty));
            T : W_Prog_Id;
         begin
               T :=
                 New_Located_Assert
                   (Ada_Node => Ada_Node,
                    Reason   => To_VC_Kind (Check_Kind),
                    Pred     =>
                       (if Is_Discrete_Type (Ty) then
                        +New_Dynamic_Property (Domain => EW_Prog,
                                               Ty     => Ty,
                                               Expr   => Expr)
                        else New_Call
                          (Name   =>
                               Prefix (M        => M,
                                       W        => WNE_Range_Pred,
                                       Ada_Node => Ty),
                           Args   => (1 => Expr))),
                    Kind     => EW_Assert);
            return
              +Binding_For_Temp (Domain => EW_Prog,
                                 Tmp    => Expr,
                                 Context => +Sequence (T, +Expr));
         end;
      else
         return +New_VC_Call (Domain   => EW_Prog,
                              Ada_Node => Ada_Node,
                              Name     =>
                                Range_Check_Name (Ty, Check_Kind),
                              Progs    => (1 => +W_Expr),
                              Reason   => To_VC_Kind (Check_Kind),
                              Typ      => Get_Type (W_Expr));
      end if;
   end Do_Range_Check;

   ------------------------------
   -- Insert_Scalar_Conversion --
   ------------------------------

   function Insert_Scalar_Conversion
     (Domain        : EW_Domain;
      Ada_Node      : Node_Id := Empty;
      Expr          : W_Expr_Id;
      To            : W_Type_Id;
      Round_Func    : W_Identifier_Id := Why_Empty;
      Do_Check      : Boolean := False) return W_Expr_Id
   is
      procedure Get_Range_Check_Info
        (Expr       : Node_Id;
         Check_Type : out Entity_Id;
         Check_Kind : out Range_Check_Kind);
      --  The frontend sets Do_Range_Check flag to True both for range checks
      --  and for index checks. We distinguish between these by calling this
      --  procedure, which also sets the bounds against which the value of Expr
      --  should be checked. Expr should have the flag Do_Range_Check flag set
      --  to True. Check_Type is set to the entity giving the bounds for the
      --  check. Check_Kind is set to an appropriate check kind, denoting a
      --  range check, an overflow check or an index check.

      --------------------------
      -- Get_Range_Check_Info --
      --------------------------

      procedure Get_Range_Check_Info
        (Expr       : Node_Id;
         Check_Type : out Entity_Id;
         Check_Kind : out Range_Check_Kind)
      is
         Par : constant Node_Id := Parent (Expr);

      begin
         --  Set the appropriate entity in Check_Type giving the bounds for the
         --  check, depending on the parent node Par.

         case Nkind (Par) is

         when N_Assignment_Statement =>
            Check_Type := Etype (Name (Par));

         --  For an array access, an index check has already been introduced
         --  if needed. There is no other check to do.

         when N_Indexed_Component =>
            Check_Type := Empty;
            Check_Kind := RCK_Index;
            return;

         --  Frontend may have introduced unchecked type conversions on
         --  expressions or variables assigned to, which require range
         --  checking. Look at the parent of the N_Unchecked_Type_Conversion
         --  node in that case.

         when N_Type_Conversion | N_Unchecked_Type_Conversion =>
            Check_Type := Etype (Par);

         when N_Qualified_Expression =>
            Check_Type := Etype (Par);

         when N_Simple_Return_Statement =>
            Check_Type :=
              Etype (Return_Applies_To (Return_Statement_Entity (Par)));

            --  For a call, retrieve the type for the corresponding argument

         when N_Function_Call            |
              N_Procedure_Call_Statement |
              N_Parameter_Association    =>
            declare
               Formal : constant Entity_Id := Get_Formal_From_Actual (Expr);
            begin

               --  ??? not particularly clean
               --  if the formal is an in parameter, the check type is always
               --  the type of the formal. Otherwise, the check type is the
               --  type to convert to.

               if Ekind (Formal) = E_In_Parameter then
                  Check_Type := Etype (Formal);
               else
                  Check_Type := Get_Ada_Node (+To);
               end if;
            end;

         when N_Attribute_Reference =>
            Attribute : declare
               Aname   : constant Name_Id := Attribute_Name (Par);
               Attr_Id : constant Attribute_Id := Get_Attribute_Id (Aname);
            begin
               case Attr_Id is
                  when Attribute_Pred |
                       Attribute_Succ |
                       Attribute_Val  =>
                     Check_Type := Base_Type (Entity (Prefix (Par)));

                  when others =>
                     Ada.Text_IO.Put_Line ("[Get_Range_Check_Info] attr ="
                                           & Attribute_Id'Image (Attr_Id));
                     raise Program_Error;
               end case;
            end Attribute;

         when N_Object_Declaration =>
            Check_Type := Etype (Defining_Identifier (Par));

         when N_Op_Expon =>

            --  A range check on exponentiation is only possible on the right
            --  operand, and in this case the check range is "Natural"

            Check_Type := Standard_Natural;

         when N_Component_Association =>

            declare
               Pref        : Node_Id;
               Prefix_Type : Entity_Id;

            begin
               --  Expr is either
               --  1) a choice of a 'Update aggregate, and needs a
               --  range check towards the corresponding index type of the
               --  prefix to the 'Update aggregate, or
               --  2) a component expression of a 'Update aggregate for arrays,
               --  and needs a range check towards the component type.
               --  3) a component expression of a 'Update aggregate for
               --  records, and needs a range check towards the type of
               --  the component
               --  3) an expression of a regular record aggregate, and
               --  needs a range check towards the expected type.

               if Nkind (Parent (Par)) = N_Aggregate
                   and then Nkind (Parent (Parent (Par))) =
                     N_Attribute_Reference
                   and then
                   Get_Attribute_Id
                     (Attribute_Name (Parent (Parent (Par)))) =
                       Attribute_Update
               then

                  Pref := Prefix (Parent (Parent (Par)));

                  --  When present, the Actual_Subtype of the entity should be
                  --  used instead of the Etype of the prefix.

                  if Is_Entity_Name (Pref)
                    and then Present (Actual_Subtype (Entity (Pref)))
                  then
                     Prefix_Type := Actual_Subtype (Entity (Pref));
                  else
                     Prefix_Type := Etype (Pref);
                  end if;

                  if Is_Record_Type (Prefix_Type) then

                     Check_Type := Etype (First (Choices (Par)));

                  --  it's an array type, determine whether the check is for
                  --  the component or the index

                  elsif Expression (Par) = Expr then
                     Check_Type :=
                       Component_Type (Unique_Entity (Prefix_Type));
                  else
                     Check_Type :=
                       Etype (First_Index (Unique_Entity (Prefix_Type)));
                  end if;

               --  must be a regular record aggregate

               else
                  pragma Assert (Expression (Par) = Expr);

                  Check_Type := Etype (Expr);
               end if;
            end;

         when N_Range =>

            Check_Type := Etype (Par);

         when N_Aggregate =>

            --  This parent is a special choice, the LHS of an association
            --  of a 'Update of a multi-dimensional array, for example:
            --  (I, J, K) of 'Update((I, J, K) => New_Val)

            pragma Assert (Nkind (Parent (Par)) = N_Component_Association);

            Aggregate : declare

               Aggr : constant Node_Id := Parent (Parent (Par));

               pragma Assert (Nkind (Aggr) = N_Aggregate
                  and then Nkind (Parent (Aggr)) = N_Attribute_Reference
                  and then Get_Attribute_Id
                    (Attribute_Name (Parent (Aggr))) = Attribute_Update);

               Pref        : constant Node_Id := Prefix (Parent (Aggr));
               Num_Dim     : constant Pos :=
                 Number_Dimensions (Type_Of_Node (Pref));
               Multi_Exprs : constant List_Id := Expressions (Par);

               Dim_Expr      : Node_Id;
               Array_Type    : Entity_Id;
               Current_Index : Node_Id;
               Found         : Boolean;

               pragma Assert (1 < Num_Dim
                                and then No (Component_Associations (Par))
                                and then List_Length (Multi_Exprs) = Num_Dim);

            begin

               --  When present, the Actual_Subtype of the entity should be
               --  used instead of the Etype of the prefix.

               if Is_Entity_Name (Pref)
                 and then Present (Actual_Subtype (Entity (Pref)))
               then
                  Array_Type := Actual_Subtype (Entity (Pref));
               else
                  Array_Type := Etype (Pref);
               end if;

               --  Find the index type for this expression's dimension.

               Dim_Expr      := Nlists.First (Multi_Exprs);
               Current_Index := First_Index (Unique_Entity (Array_Type));
               Found         := False;

               while Present (Dim_Expr) loop
                  if Expr = Dim_Expr then
                     Check_Type := Etype (Current_Index);
                     Found := True;
                     exit;
                  end if;
                  Next (Dim_Expr);
                  Next_Index (Current_Index);
               end loop;

               pragma Assert (Found);

            end Aggregate;

         when N_Aspect_Specification =>

            --  We only expect range checks on aspects for default values.

            case Get_Aspect_Id (Par) is
            when Aspect_Default_Component_Value =>
               pragma Assert (Is_Array_Type (Entity (Par)));
               Check_Type := Component_Type (Entity (Par));
            when Aspect_Default_Value =>
               pragma Assert (Is_Scalar_Type (Entity (Par)));
               Check_Type := Entity (Par);
            when others =>
               Ada.Text_IO.Put_Line ("[Get_Range_Check_Info] aspect ="
                                     & Aspect_Id'Image (Get_Aspect_Id (Par)));
               raise Program_Error;
            end case;

         when N_Component_Declaration | N_Discriminant_Specification =>

            --  We expect range checks on defaults of record fields and
            --  discriminants.

            Check_Type := Etype (Defining_Identifier (Par));

         when others =>
            Ada.Text_IO.Put_Line ("[Get_Range_Check_Info] kind ="
                                  & Node_Kind'Image (Nkind (Par)));
            raise Program_Error;
         end case;

         --  Reach through a non-private type in order to query its kind

         Check_Type := MUT (Check_Type);

         --  If the target type is a constrained array, we have a length check.

         if Is_Array_Type (Check_Type) and then
           Is_Constrained (Check_Type)
         then
            Check_Kind := RCK_Length;

         --  For attributes Pred and Succ, the check is a range check for
         --  enumeration types, and an overflow check otherwise. We use special
         --  values of Check_Kind to account for the different range checked in
         --  these cases.

         elsif Nkind (Par) = N_Attribute_Reference and then
           Get_Attribute_Id (Attribute_Name (Par)) = Attribute_Pred
         then
            if Is_Enumeration_Type (Check_Type) then
               Check_Kind := RCK_Range_Not_First;
            else
               Check_Kind := RCK_Overflow_Not_First;
            end if;

         elsif Nkind (Par) = N_Attribute_Reference and then
           Get_Attribute_Id (Attribute_Name (Par)) = Attribute_Succ
         then
            if Is_Enumeration_Type (Check_Type) then
               Check_Kind := RCK_Range_Not_Last;
            else
               Check_Kind := RCK_Overflow_Not_Last;
            end if;

         --  Otherwise, this is a range check

         else
            Check_Kind := RCK_Range;
         end if;
      end Get_Range_Check_Info;

      From : constant W_Type_Id := Get_Type (Expr);

      --  Current result expression

      --  Type and kind for the range check
      Range_Type : Entity_Id := Empty;
      Check_Kind : Range_Check_Kind := RCK_Range;

   --  Start of Insert_Scalar_Conversion

   begin
      --  Do nothing when
      --  1. From = To, and
      --  2. no rounding needed, and
      --  3. a) no check needed, _or_
      --     b) check is flagged but the base type is the one reserved for
      --        Standard.Boolean, so check does not need to be inserted.
      --        (Other boolean types in Ada have a base type of EW_Int.)

      if Eq_Base (To, From)
        and then (not Do_Check
                    or else  Get_Base_Type (To) = EW_Bool)
        and then No (Round_Func)
      then
         return Expr;
      end if;

      --  Retrieve range check information

      if Do_Check then
         Get_Range_Check_Info (Ada_Node, Range_Type, Check_Kind);
      end if;

      return Insert_Scalar_Conversion
        (Domain      => Domain,
         Ada_Node    => Ada_Node,
         Expr        => Expr,
         To          => To,
         Round_Func  => Round_Func,
         Range_Type  => Range_Type,
         Check_Kind  => Check_Kind);
   end Insert_Scalar_Conversion;

   function Insert_Scalar_Conversion
     (Domain        : EW_Domain;
      Ada_Node      : Node_Id := Empty;
      Expr          : W_Expr_Id;
      To            : W_Type_Id;
      Round_Func    : W_Identifier_Id := Why_Empty;
      Range_Type    : Entity_Id;
      Check_Kind    : Range_Check_Kind) return W_Expr_Id
   is

      From : constant W_Type_Id := Get_Type (Expr);

      --  Current result expression
      Result : W_Expr_Id := Expr;

      --  Current type of the result expression
      Cur : W_Type_Id := From;

      --  Set to True after range check has been applied
      Range_Check_Applied : Boolean := False;

   --  Start of Insert_Scalar_Conversion

   begin

      --  If the check is a range check on a floating-point type, and we can
      --  determine that the expression is always within bounds, then issue a
      --  check always true.

      if Present (Range_Type)
        and then Is_Floating_Point_Type (Range_Type)
      then
         declare
            Tlo : constant Node_Id := Type_Low_Bound  (Range_Type);
            Thi : constant Node_Id := Type_High_Bound (Range_Type);
            Lov : Ureal;
            Hiv : Ureal;
            Lo  : Ureal;
            Hi  : Ureal;
            OK  : Boolean;

         begin
            --  The computation of the range assumes at worst that the type of
            --  the expression is respected, so it is not suitable for overflow
            --  checks, for example the overflow check on 'Pred and 'Succ,
            --  therefore test first that Check_Kind is a range check.

            if Check_Kind = RCK_Range

              --  We can only remove the check if we can compute the expected
              --  bounds of the Range_Type now.

              and then Compile_Time_Known_Value (Tlo)
              and then Compile_Time_Known_Value (Thi)
            then
               Lov := Expr_Value_R (Tlo);
               Hiv := Expr_Value_R (Thi);

               Determine_Range_R
                 (Ada_Node, OK, Lo, Hi, Assume_Valid => True);

               if OK then

                  --  If definitely in range, generate a check always true for
                  --  the range check. When gnat2why directly handles check
                  --  messages, a message could be generated instead here.

                  if Lo >= Lov and then Hi <= Hiv then
                     Emit_Always_True_Range_Check (Ada_Node, Check_Kind);
                     Range_Check_Applied := True;
                  end if;
               end if;
            end if;
         end;
      end if;

      --  The regular case, we take care to insert the range check at a
      --  valid place where the expression is of the appropriate Why base
      --  type (real for a range check of a floating point type, int for a
      --  range check of a discrete type).

      --  1. If From is an abstract type, convert it to type int, __fixed or
      --     real.

      if Get_Base_Type (From) = EW_Abstract then
         Cur := Base_Why_Type (From);
         Result := Insert_Single_Conversion (Ada_Node => Ada_Node,
                                             Domain   => Domain,
                                             To       => Cur,
                                             Expr     => Result);
      end if;

      --  2. Possibly perform the range check, if applicable on Cur. A special
      --     case is that range checks on boolean variables are performed after
      --     their conversion to int.

      if Present (Range_Type)
        and then not Range_Check_Applied
        and then Base_Why_Type (Range_Type) = Cur
        and then Get_Base_Type (From) /= EW_Bool
      then
         Range_Check_Applied := True;

         Result := +Do_Range_Check (Ada_Node   => Ada_Node,
                                    Ty         => Range_Type,
                                    W_Expr     => Result,
                                    Check_Kind => Check_Kind);
      end if;

      --  3. If From and To do not share the same base type (bool, int, __fixed
      --     or real), convert from one to the other.

      if Base_Why_Type (From) /= Base_Why_Type (To) then
         declare
            Shadow_From : W_Type_Id := Cur;
            Shadow_To   : W_Type_Id := Base_Why_Type (To);
            Fixed_Type  : Entity_Id;

         begin
            --  3.1. If From is a fixed-point type, retrieve the corresponding
            --       abstract type, for which conversion to int/real is
            --       defined.

            if Get_Base_Type (Base_Why_Type (From)) = EW_Fixed then
               Fixed_Type :=
                 (if Nkind (Ada_Node) in N_Type_Conversion
                                       | N_Qualified_Expression
                  then
                     Etype (Expression (Ada_Node))
                  else
                     Etype (Ada_Node));
               Shadow_From := EW_Abstract (Fixed_Type);
               pragma Assert (Get_Base_Type (Shadow_From) = EW_Abstract);

            --  3.2. If To is a fixed-point type, retrieve the corresponding
            --       abstract type, for which conversion from int/real is
            --       defined.

            elsif Get_Base_Type (Base_Why_Type (To)) = EW_Fixed then
               Fixed_Type :=
                 (if Nkind (Parent (Ada_Node)) in N_Type_Conversion
                                                | N_Qualified_Expression
                  then
                    Etype (Parent (Ada_Node))
                  else
                    Etype (Ada_Node));
               Shadow_To := EW_Abstract (Fixed_Type);
               pragma Assert (Get_Base_Type (Shadow_To) = EW_Abstract);
            end if;

            Cur := Base_Why_Type (To);
            Result := Insert_Single_Conversion (Ada_Node => Ada_Node,
                                                Domain   => Domain,
                                                From     => Shadow_From,
                                                To       => Shadow_To,
                                                Expr     => Result);
         end;
      end if;

      --  4. When converting to a floating-point type, always perform
      --     a rounding operation.

      if Present (Round_Func) then
         pragma Assert (Get_Base_Type (Cur) = EW_Real);
         Result := New_Call (Domain   => Domain,
                             Name     => Round_Func,
                             Args     => (1 => Result),
                             Typ      => EW_Real_Type);
      end if;

      --  5. Possibly perform the range check, if not already applied

      if Present (Range_Type)
        and then not Range_Check_Applied
      then
         pragma Assert (Base_Why_Type (Range_Type) = Cur
                          or else
                        Base_Why_Type (Range_Type) = EW_Bool_Type);
         Result := +Do_Range_Check (Ada_Node   => Ada_Node,
                                    Ty         => Range_Type,
                                    W_Expr     => Result,
                                    Check_Kind => Check_Kind);
      end if;

      --  6. If To is an abstract type, convert from int, __fixed or real to it

      if Get_Base_Type (To) = EW_Abstract then
         Result := Insert_Single_Conversion (Ada_Node => Ada_Node,
                                             Domain   => Domain,
                                             From     => Cur,
                                             To       => To,
                                             Expr     => Result);
      end if;

      return Result;
   end Insert_Scalar_Conversion;

   ------------------------------
   -- Insert_Simple_Conversion --
   ------------------------------

   function Insert_Simple_Conversion
     (Ada_Node : Node_Id := Empty;
      Domain   : EW_Domain;
      Expr     : W_Expr_Id;
      To       : W_Type_Id) return W_Expr_Id
   is
      From : constant W_Type_Id := Get_Type (Expr);
   begin
      --  Nothing to do if From = To

      if Eq_Base (To, From) then
         return Expr;
      end if;

      if Is_Private_Conversion (To, From) then
         return Insert_Private_Conversion (Domain     => Domain,
                                           Ada_Node   => Ada_Node,
                                           Expr       => Expr,
                                           To         => To);

      elsif Is_Record_Conversion (To, From) then
         return Insert_Record_Conversion (Domain   => Domain,
                                          Ada_Node => Ada_Node,
                                          Expr     => Expr,
                                          To       => To);

      elsif Is_Array_Conversion (To, From) then
         return Insert_Array_Conversion (Domain   => Domain,
                                         Ada_Node => Ada_Node,
                                         Expr     => Expr,
                                         To       => To);

      else
         return Insert_Scalar_Conversion (Domain   => Domain,
                                          Ada_Node => Ada_Node,
                                          Expr     => Expr,
                                          To       => To);
      end if;
   end Insert_Simple_Conversion;

   ------------------------------
   -- Insert_Single_Conversion --
   ------------------------------

   function Insert_Single_Conversion
     (Ada_Node : Node_Id;
      Domain   : EW_Domain;
      To       : W_Type_Id;
      Expr     : W_Expr_Id) return W_Expr_Id
   is
      From : constant W_Type_Id := Get_Type (Expr);
   begin
      return Insert_Single_Conversion (Ada_Node => Ada_Node,
                                       Domain   => Domain,
                                       From     => From,
                                       To       => To,
                                       Expr     => Expr);
   end Insert_Single_Conversion;

   function Insert_Single_Conversion
     (Ada_Node : Node_Id;
      Domain   : EW_Domain;
      From     : W_Type_Id;
      To       : W_Type_Id;
      Expr     : W_Expr_Id) return W_Expr_Id is
   begin
      if Eq_Base (From, To) then
         return Expr;
      end if;

      return
        New_Call (Domain   => Domain,
                  Ada_Node => Ada_Node,
                  Name     => Conversion_Name (From => From, To => To),
                  Args     => (1 => +Expr),
                  Typ      => To);
   end Insert_Single_Conversion;

   ----------------------
   -- Is_False_Boolean --
   ----------------------

   function Is_False_Boolean (P : W_Expr_Id) return Boolean
   is
   begin
      return
         (Get_Kind (+P) = W_Literal and then
          Get_Value (+P) = EW_False);
   end Is_False_Boolean;

   ---------------------
   -- Is_True_Boolean --
   ---------------------

   function Is_True_Boolean (P : W_Expr_Id) return Boolean
   is
   begin
      return
         (Get_Kind (+P) = W_Literal and then
          Get_Value (+P) = EW_True);
   end Is_True_Boolean;

   ----------------------
   -- New_Ada_Equality --
   ----------------------

   function New_Ada_Equality
     (Typ              : Entity_Id;
      Domain           : EW_Domain;
      Left, Right      : W_Expr_Id;
      Force_Predefined : Boolean := False)
      return W_Expr_Id is
      Why_Type : constant W_Type_Id := EW_Abstract (Typ);
      Use_Predef : constant Boolean :=
        Force_Predefined or else not Present (Has_User_Defined_Eq (Typ));
      Eq_Str   : constant String :=
        (if Use_Predef then "bool_eq" else "user_eq");
      Module   : constant W_Module_Id :=
        (if Is_Boolean_Type (Typ) then Boolean_Module else E_Module (Typ));
      Eq_Id    : constant W_Identifier_Id :=
        New_Identifier (Module   => Module,
                        Name     => Eq_Str,
                        Typ      => EW_Bool_Type,
                        Ada_Node => Typ);
      Is_Pred  : Boolean := False;
      T        : W_Expr_Id;
   begin
      if Is_Scalar_Type (Typ) then
         declare
            Left_Int : constant W_Expr_Id :=
              Insert_Simple_Conversion
                (Domain => EW_Term,
                 Expr => Left,
                 To   => Base_Why_Type (Why_Type));
            Right_Int : constant W_Expr_Id :=
              Insert_Simple_Conversion
                (Domain => EW_Term,
                 Expr => Right,
                 To   => Base_Why_Type (Why_Type));
         begin
            if Use_Predef then
               T :=
                 New_Relation
                   (Domain  => Domain,
                    Op      => EW_Eq,
                    Op_Type => Get_Base_Type (Base_Why_Type (Why_Type)),
                    Left    => Left_Int,
                    Right   => Right_Int);
               Is_Pred := True;
            else
               T :=
                 New_Call
                   (Name   => Eq_Id,
                    Domain => EW_Term,
                    Args   => (1 => Left_Int, 2 => Right_Int),
                    Typ   => EW_Bool_Type);
            end if;
         end;
      else
         T :=
           New_Call
             (Name   => Eq_Id,
              Domain => EW_Term,
              Args   =>
                (1 => Left,
                 2 => Right),
              Typ   => EW_Bool_Type);
      end if;
      if Is_Pred then
         return T;
      else
         return
           New_Relation
             (Op_Type => EW_Bool,
              Domain  => Domain,
              Op      => EW_Eq,
              Left    => T,
              Right   => Bool_True (EW_Term));
      end if;
   end New_Ada_Equality;

   ------------------
   -- New_And_Expr --
   ------------------

   function New_And_Expr
      (Left, Right : W_Expr_Id;
       Domain      : EW_Domain) return W_Expr_Id is
   begin
      if Is_True_Boolean (+Left) then
         return Right;

      elsif Is_True_Boolean (+Right) then
         return Left;

      elsif Domain = EW_Pred then
         return New_Connection (Domain => Domain,
                                Op     => EW_And,
                                Left   => +Left,
                                Right  => +Right);
      else
         return New_Call (Domain => Domain,
                          Name   => To_Ident (WNE_Bool_And),
                          Args   => (1 => +Left, 2 => +Right),
                          Typ    => EW_Bool_Type);
      end if;
   end New_And_Expr;

   function New_And_Expr
      (Conjuncts : W_Expr_Array;
       Domain    : EW_Domain) return W_Expr_Id is
   begin
      if Conjuncts'Length = 0 then
         return +False_Pred;

      elsif Conjuncts'Length = 1 then
         return Conjuncts (Conjuncts'First);

      elsif Domain = EW_Pred then
         return New_Connection
           (Domain     => Domain,
            Op         => EW_And,
            Left       => +Conjuncts (Conjuncts'First),
            Right      => +Conjuncts (Conjuncts'First + 1),
            More_Right => Conjuncts (Conjuncts'First + 2 .. Conjuncts'Last));

      else
         declare
            Result : W_Expr_Id :=
              New_Call (Domain => Domain,
                        Name   => To_Ident (WNE_Bool_And),
                        Args   => (1 => +Conjuncts (Conjuncts'First),
                                   2 => +Conjuncts (Conjuncts'First + 1)),
                        Typ    => EW_Bool_Type);
         begin
            for K in Conjuncts'First + 2 .. Conjuncts'Last loop
               Result := New_Call (Domain => Domain,
                                   Name   => To_Ident (WNE_Bool_And),
                                   Args   => (1 => Result,
                                              2 => +Conjuncts (K)),
                                   Typ    => EW_Bool_Type);
            end loop;

            return Result;
         end;
      end if;
   end New_And_Expr;

   function New_And_Expr
      (Left, Right : W_Expr_Id;
       Domain      : EW_Domain;
       Base        : W_Type_Id) return W_Expr_Id is
   begin
      if Base = EW_Bool_Type then
         return New_And_Expr (Left, Right, Domain);
      else
         return
           New_Call (Domain => Domain,
                     Name   => Integer_Bitwise_And,
                     Args   => (1 => +Left, 2 => +Right),
                     Typ    => EW_Int_Type);
      end if;
   end New_And_Expr;

   -----------------------
   -- New_And_Then_Expr --
   -----------------------

   function New_And_Then_Expr
      (Left, Right : W_Expr_Id;
       Domain      : EW_Domain) return W_Expr_Id is
   begin
      if Is_True_Boolean (+Left) then
         return Right;
      elsif Is_True_Boolean (+Right) then
         return Left;
      else
         if Domain = EW_Prog then
            return
               New_Connection
                 (Op     => EW_And_Then,
                  Left   => Left,
                  Right  => Right,
                  Domain => Domain);
         else
            return New_And_Expr (Left, Right, Domain);
         end if;
      end if;
   end New_And_Then_Expr;

   ------------------------
   -- New_Attribute_Expr --
   ------------------------

   function New_Attribute_Expr
     (Ty     : Entity_Id;
      Attr   : Supported_Attribute_Id;
      Params : Transformation_Params := Body_Params) return W_Expr_Id is
   begin
      if Attr in Attribute_First | Attribute_Last
        and then ((not Is_Static_Subtype (Ty) and then Is_Discrete_Type (Ty))
                  or else Type_Is_Modeled_As_Int_Or_Real (Ty))
      then
         --  Use expression for dynamic bounds

         declare
            Rng       : constant Node_Id := Get_Range (Ty);
            BT        : constant W_Type_Id :=
              (if Is_Standard_Boolean_Type (Ty) then EW_Int_Type
               else Base_Why_Type (Ty));
         begin
            if Attr = Attribute_First then
               return Transform_Expr (Low_Bound (Rng), BT, EW_Term, Params);
            else
               return Transform_Expr (High_Bound (Rng), BT, EW_Term, Params);
            end if;
         end;

      elsif Attr in Attribute_First | Attribute_Last | Attribute_Length
        and then Ekind (Ty) = E_String_Literal_Subtype
      then
         case Attr is
            when Attribute_First =>
               return New_Integer_Constant
                 (Value => Expr_Value (String_Literal_Low_Bound (Ty)));
            when Attribute_Length =>
               return New_Integer_Constant
                 (Value => String_Literal_Length (Ty));
            when Attribute_Last =>
               return
                 New_Integer_Constant
                   (Value =>
                       Expr_Value (String_Literal_Low_Bound (Ty)) +
                      String_Literal_Length (Ty) - 1);
            when others =>
               raise Program_Error;
         end case;
      else
         declare
            M : constant W_Module_Id :=
              (if Is_Standard_Boolean_Type (Ty) then Boolean_Module
               else E_Module (Ty));
            T : W_Expr_Id;
            BT : constant W_Type_Id :=
              (case Attr is
                  when Attribute_First
                     | Attribute_Last
                     | Attribute_Modulus
                     | Attribute_Value
                     =>
                     (if Is_Standard_Boolean_Type (Ty) then
                        EW_Int_Type
                      else Base_Why_Type (Ty)),
                  when Attribute_Length =>
                     EW_Int_Type,
                  when Attribute_Image =>
                     String_Image_Type,
                  when Attribute_Constrained =>
                     EW_Bool_Type,
                  when Attribute_Size =>
                     EW_Int_Type,
                  when Attribute_Tag =>
                     EW_Int_Type);
         begin
            T := +Prefix (Ada_Node => Ty,
                          M        => M,
                          W        => Attr_To_Why_Name (Attr),
                          Typ      => BT);

            return T;
         end;
      end if;
   end New_Attribute_Expr;

   --------------------
   -- New_Comparison --
   --------------------

   function New_Comparison
     (Cmp         : EW_Relation;
      Left, Right : W_Expr_Id;
      Domain      : EW_Domain)
     return W_Expr_Id
   is
      Op_Type  : W_Type_Id;
      Left1    : W_Expr_Id;
      Right1   : W_Expr_Id;
      Arg_Type : constant W_Type_Id := Get_Type (Left);

   begin
      --  The only comparisons between Boolean operands that we translate in
      --  Why without going throught integers are the equality and inequality
      --  in a predicate context, translated as equivalence or inequivalence.

      if Get_Base_Type (Arg_Type) = EW_Bool
        and then (Cmp in EW_Inequality or else Domain /= EW_Pred)
      then
         Op_Type := EW_Int_Type;
         Left1  :=
           Insert_Simple_Conversion
             (Domain => Domain,
              Expr   => Left,
              To     => EW_Int_Type);
         Right1 :=
           Insert_Simple_Conversion
             (Domain => Domain,
              Expr   => Right,
              To     => EW_Int_Type);
      else
         Op_Type := Arg_Type;
         Left1  := Left;
         Right1 := Right;
      end if;

      if Domain in EW_Pred | EW_Prog then
         return
           New_Relation
             (Domain  => Domain,
              Op_Type => Get_Base_Type (Op_Type),
              Left    => +Left1,
              Right   => +Right1,
              Op      => Cmp);
      else
         return
           New_Call
             (Name   => New_Bool_Cmp (Cmp, Op_Type),
              Args   => (1 => +Left1, 2 => +Right1),
              Domain => Domain,
              Typ    => EW_Bool_Type);
      end if;
   end New_Comparison;

   --------------------------
   -- New_Dynamic_Property --
   --------------------------

   function New_Dynamic_Property
     (Domain : EW_Domain;
      Ty     : Entity_Id;
      Expr   : W_Expr_Id) return W_Expr_Id
   is
   begin

      --  For now, only supports dynamic discrete types, unconstrained array
      --  types and record or private types with discriminants.

      if Is_Discrete_Type (Ty) then

         pragma Assert (not Depends_On_Discriminant (Get_Range (Ty)));

         return New_Call (Domain => Domain,
                          Name   => Dynamic_Prop_Name (Ty),
                          Args   => (1 => New_Attribute_Expr
                                     (Ty     => Ty,
                                      Attr   => Attribute_First,
                                      Params => Body_Params),
                                     2 => New_Attribute_Expr
                                       (Ty     => Ty,
                                        Attr   => Attribute_Last,
                                        Params => Body_Params),
                                     3 =>
                                       Insert_Simple_Conversion
                                         (Ada_Node => Ty,
                                          Domain   => Domain,
                                          Expr     => Expr,
                                          To       => EW_Int_Type)),
                          Typ    => EW_Bool_Type);
      elsif Is_Array_Type (Ty) and then not Is_Static_Array_Type (Ty) then
         declare
            Dim   : constant Positive := Positive (Number_Dimensions (Ty));
            Args  : W_Expr_Array (1 .. 4 * Dim);
         begin
            for Count in 0 .. Dim - 1 loop
               declare
                  First_Expr : constant W_Expr_Id :=
                    Get_Array_Attr (Ty     => Ty,
                                    Attr   => Attribute_First,
                                    Dim    => Count + 1);
                  Last_Expr : constant W_Expr_Id :=
                    Get_Array_Attr (Ty     => Ty,
                                    Attr   => Attribute_Last,
                                    Dim    => Count + 1);
               begin
                  Args (4 * Count + 1) := First_Expr;
                  Args (4 * Count + 2) := Last_Expr;
                  Args (4 * Count + 3) :=
                    Insert_Simple_Conversion
                      (Ada_Node => Ty,
                       Domain   => Domain,
                       Expr     => Get_Array_Attr
                         (Domain => Domain,
                          Expr   => Expr,
                          Attr   => Attribute_First,
                          Dim    => Count + 1),
                       To       => EW_Int_Type);
                  Args (4 * Count + 4) :=
                    Insert_Simple_Conversion
                      (Ada_Node => Ty,
                       Domain   => Domain,
                       Expr     => Get_Array_Attr
                         (Domain => Domain,
                          Expr   => Expr,
                          Attr   => Attribute_Last,
                          Dim    => Count + 1),
                       To       => EW_Int_Type);
               end;
            end loop;

            return New_Call (Domain => Domain,
                             Name   => Dynamic_Prop_Name (Ty),
                             Args   => Args,
                             Typ    => EW_Bool_Type);
         end;
      elsif Has_Discriminants (Ty) and then Is_Constrained (Ty) then
         declare
            Base_Expr : constant W_Expr_Id :=
              (if Is_Record_Type (Ty) then
                    Insert_Single_Conversion (Domain   => EW_Term,
                                              Ada_Node => Ty,
                                              To       =>
                                                EW_Abstract
                                                  (Root_Record_Type (Ty)),
                                              Expr     => Expr)
               else Expr);
         begin
            return New_Call
              (Name   => Range_Pred_Name (Ty),
               Args   => Prepare_Args_For_Subtype_Check (Ty, Base_Expr),
               Domain => Domain,
               Typ    => EW_Bool_Type);
         end;
      else
         raise Program_Error;
      end if;
   end New_Dynamic_Property;

   -----------------
   -- New_Int_Add --
   -----------------

   function New_Int_Add
     (Domain : EW_Domain;
      Left   : W_Expr_Id;
      Right  : W_Expr_Id) return W_Expr_Id is
   begin
      return
        New_Binary_Op
          (Op      => EW_Add,
           Op_Type => EW_Int,
           Left    =>
             Insert_Scalar_Conversion
               (Domain => Domain,
                Expr   => Left,
                To     => EW_Int_Type),
           Right   =>
             Insert_Scalar_Conversion
               (Domain => Domain,
                Expr   => Right,
                To     => EW_Int_Type));
   end New_Int_Add;

   -----------------------
   -- New_Int_Substract --
   -----------------------

   function New_Int_Substract
     (Domain : EW_Domain;
      Left   : W_Expr_Id;
      Right  : W_Expr_Id) return W_Expr_Id is
   begin
      return
        New_Binary_Op
          (Op      => EW_Substract,
           Op_Type => EW_Int,
           Left    =>
             Insert_Scalar_Conversion
               (Domain => Domain,
                Expr   => Left,
                To     => EW_Int_Type),
           Right   =>
             Insert_Scalar_Conversion
               (Domain => Domain,
                Expr   => Right,
                To     => EW_Int_Type));
   end New_Int_Substract;

   -----------------------
   -- New_Located_Label --
   -----------------------

   function New_Located_Label
     (N         : Node_Id;
      Left_Most : Boolean := False)
      return Name_Id
   is
      Slc    : Source_Ptr;
      Buf    : Unbounded_String := Null_Unbounded_String;
      Prefix : constant String := "GP_Sloc:";
   begin

      --  For VCs, we mostly want to point directly to the relevant node [N].
      --  For other nodes (e.g. pretty printing labels) it's more sensible to
      --  point to the beginning of the expression instead of the operator.
      --  This is achieved by calling [First_Sloc] instead of [Sloc]. However,
      --  [First_Sloc] does not work for N_And_Then nodes in assertions which
      --  are rewritten in a strange manner, so we do not do this optimization
      --  in that case. See also [New_Pretty_Label].

      if not Left_Most
            or else
         (Comes_From_Source (N)
           and then Original_Node (N) /= N
           and then Nkind (Original_Node (N)) = N_And_Then)
      then
         Slc := Sloc (N);

      --  First_Sloc does some magic to point before the opening parentheses in
      --  an expression, which does not work on locations inside instances of
      --  generics. Use Sloc on First_Node instead in that case.

      elsif Instantiation_Location (Sloc (N)) /= No_Location then
         Slc := Sloc (First_Node (N));
      else
         Slc := First_Sloc (N);
      end if;

      loop
         declare
            File   : constant String := File_Name (Slc);
            Line   : constant Physical_Line_Number :=
              Get_Physical_Line_Number (Slc);
            Column : constant Column_Number := Get_Column_Number (Slc);
         begin
            Append (Buf, File);
            Append (Buf, ':');
            Append (Buf, Int_Image (Integer (Line)));
            Append (Buf, ':');
            Append (Buf, Int_Image (Integer (Column)));
            exit when Instantiation_Location (Slc) = No_Location;
            Append (Buf, ':');
            if Comes_From_Inlined_Body (Slc) then
               Append (Buf, "inlined");
            else
               Append (Buf, "instantiated");
            end if;
            Append (Buf, ':');
            Slc := Instantiation_Location (Slc);
         end;
      end loop;
      return NID (Prefix & To_String (Buf));
   end New_Located_Label;

   --------------------
   -- New_Shape_Label --
   --------------------

   function New_Shape_Label (Node : Node_Id) return Name_Id is

      function Label_Append (Buf : Unbounded_String) return
        Unbounded_String is
          (if Buf /= Null_Unbounded_String then "__" & Buf
           else Null_Unbounded_String);

      GP_Prefix : constant String := "GP_Shape:";
      Buf : Unbounded_String := Null_Unbounded_String;
      Node_It : Node_Id := Node;
   begin
      while Present (Node_It) loop
         case Nkind (Node_It) is

         when N_Subprogram_Body | N_Subprogram_Specification
            | N_Expression_Function | N_Package_Body
            | N_Package_Specification | N_Generic_Subprogram_Declaration =>
            exit;

         when N_Loop_Statement =>
            declare
               It_Scheme : constant Node_Id := Iteration_Scheme (Node_It);
            begin
               if Present (It_Scheme) then
                  case Nkind (It_Scheme) is
                  when N_Loop_Parameter_Specification
                     | N_Iterator_Specification =>
                     --  for
                     Buf := "for" & Label_Append (Buf);
                  when others =>
                     --  while
                     Buf := "while" & Label_Append (Buf);
                  end case;
               else
                  --  loop
                  Buf := "loop" & Label_Append (Buf);
               end if;
            end;

            if Identifier (Node_It) /= Empty then
               Buf := Get_Name_String (Chars (Identifier (Node_It)))
                 & "_" & Buf;
            end if;

         when N_Case_Statement | N_Case_Expression =>
            Buf := "case" & Label_Append (Buf);

         when N_If_Statement | N_If_Expression =>
            Buf := "if" & Label_Append (Buf);

         when N_Enumeration_Representation_Clause =>
            Buf := Get_Name_String (Chars (Identifier (Node_It)))
              & "_rep" & Label_Append (Buf);
         when N_At_Clause =>
            Buf := Get_Name_String (Chars (Identifier (Node_It)))
              & "_at" & Label_Append (Buf);
         when N_Record_Representation_Clause =>
            Buf := Get_Name_String (Chars (Identifier (Node_It)))
              & "_" & Buf;
         when N_Component_Clause =>
            Buf := Get_Name_String (Chars (Component_Name (Node_It)))
              & "_rep" & Label_Append (Buf);
         when N_Mod_Clause =>
            Buf := "modrep" & Label_Append (Buf);

         when N_Attribute_Definition_Clause =>
            Buf := Get_Name_String (Chars (Name (Node_It))) & "_"
              & Get_Name_String (Chars (Node_It))
              & "_def" & Label_Append (Buf);

         when N_Pragma_Argument_Association =>
            Buf := "pragargs" & Label_Append (Buf);

         when N_Op_Add =>
            Buf := "add" & Label_Append (Buf);
         when N_Op_Concat =>
            Buf := "concat" & Label_Append (Buf);
         when N_Op_Expon =>
            Buf := "exp" & Label_Append (Buf);
         when N_Op_Subtract =>
            Buf := "sub" & Label_Append (Buf);
         when N_Op_Divide =>
            Buf := "div" & Label_Append (Buf);
         when N_Op_Mod =>
            Buf := "mod" & Label_Append (Buf);
         when N_Op_Multiply =>
            Buf := "mult" & Label_Append (Buf);
         when N_Op_Rem =>
            Buf := "rem" & Label_Append (Buf);
         when N_Op_And =>
            Buf := "and" & Label_Append (Buf);
         when N_Op_Compare =>
            Buf := "cmp" & Label_Append (Buf);
         when N_Op_Or =>
            Buf := "or" & Label_Append (Buf);
         when N_Op_Xor =>
            Buf := "xor" & Label_Append (Buf);

         when N_Op_Rotate_Left =>
            Buf := "rol" & Label_Append (Buf);
         when N_Op_Rotate_Right =>
            Buf := "ror" & Label_Append (Buf);
         when N_Op_Shift_Left =>
            Buf := "lsl" & Label_Append (Buf);
         when N_Op_Shift_Right =>
            Buf := "lsr" & Label_Append (Buf);
         when N_Op_Shift_Right_Arithmetic =>
            Buf := "asr" & Label_Append (Buf);
         when N_Op_Abs =>
            Buf := "abs" & Label_Append (Buf);
         when N_Op_Minus =>
            Buf := "minus" & Label_Append (Buf);
         when N_Op_Not =>
            Buf := "not" & Label_Append (Buf);
         when N_Op_Plus =>
            Buf := "plus" & Label_Append (Buf);

         when N_Attribute_Reference =>
            Buf := Get_Name_String (Attribute_Name (Node_It))
              & "_ref" & Label_Append (Buf);

         when N_Membership_Test =>
            Buf := "in" & Label_Append (Buf);

         when N_And_Then =>
            Buf := "andthen" & Label_Append (Buf);
         when N_Or_Else =>
            Buf := "orelse" & Label_Append (Buf);

         when N_Subprogram_Call =>
            Buf := "call_" & Get_Name_String (Chars (Name (Node_It)))
              & Label_Append (Buf);

         when N_Indexed_Component =>
            Buf := "ixdcomp" & Label_Append (Buf);

         when N_Null =>
            Buf := "null" & Label_Append (Buf);

         when N_Qualified_Expression =>
            Buf := Get_Name_String (Chars (Subtype_Mark (Node_It)))
                                    & "_qual" & Label_Append (Buf);

         when N_Quantified_Expression =>
            Buf := (if All_Present (Node_It) then "forall" else "forsome")
              & Label_Append (Buf);

         when N_Aggregate =>
            Buf := "aggr" & Label_Append (Buf);

         when N_Allocator =>
            Buf := "new_" & Buf;

         when N_Raise_Expression =>
            Buf := "raise" & Label_Append (Buf);

         when N_Range =>
            Buf := "range" & Label_Append (Buf);

         when N_Selected_Component =>
            Buf := "selectcomp" & Label_Append (Buf);

         when N_Slice =>
            Buf := "slice" & Label_Append (Buf);

         when N_Type_Conversion | N_Unchecked_Type_Conversion =>
            Buf := "typeconv" & Label_Append (Buf);

         when N_Subtype_Indication =>
            Buf := Get_Name_String (Chars (Subtype_Mark (Node_It)))
              & "_ind" & Label_Append (Buf);

         when N_Formal_Type_Declaration | N_Implicit_Label_Declaration
            | N_Object_Declaration | N_Formal_Object_Declaration =>
            declare
               I_Name : constant Name_Id := Chars (Defining_Identifier
                                                   (Node_It));
               Name_Str : constant String :=
                 (if I_Name /= No_Name and then I_Name /= Error_Name then
                     Get_Name_String (I_Name) & "_"
                  else "");
            begin
               Buf := Name_Str & "decl" & Label_Append (Buf);
            end;

         when N_Full_Type_Declaration | N_Incomplete_Type_Declaration
            | N_Protected_Type_Declaration | N_Private_Type_Declaration
            | N_Subtype_Declaration =>
            Buf :=  Get_Name_String (Chars (Defining_Identifier (Node_It)))
              & "_def" & Label_Append (Buf);

         when N_Private_Extension_Declaration =>
            Buf := Get_Name_String (Chars (Defining_Identifier (Node_It)))
              & "_priv" & Label_Append (Buf);

         when N_Body_Stub =>
            Buf := Get_Name_String (Chars (Defining_Identifier (Node_It)))
              & "_stub" & Label_Append (Buf);

         when N_Generic_Instantiation =>
            Buf := Get_Name_String (Chars (Defining_Identifier (Node_It)))
              & "_inst" & Label_Append (Buf);

         when N_Array_Type_Definition =>
            Buf := "arrayof_" & Buf;

         when N_Assignment_Statement =>
            declare
               I_Name : constant Name_Id := Chars (Defining_Identifier
                                                   (Node_It));
               Name_Str : constant String :=
                 (if I_Name /= No_Name and then I_Name /= Error_Name then
                     Get_Name_String (I_Name) & "_"
                  else "");
            begin
               Buf := Name_Str & "assign" & Label_Append (Buf);
            end;

         when N_Block_Statement =>
            declare
               Tmp : constant String := (if Identifier (Node_It) /= Empty
                                         then
                                            Get_Name_String
                                           (Chars (Identifier (Node_It))) & "_"
                                         else "");
            begin
               Buf := Tmp & "declblk" & Label_Append (Buf);
            end;

         when N_Goto_Statement =>
            Buf := "goto_" & Get_Name_String (Chars (Name (Node_It)))
              & Label_Append (Buf);

         when N_Raise_Statement =>
            Buf := "raise" & (if Name (Node_It) /= Empty then
                                 "_" & Get_Name_String
                                (Chars (Name (Node_It)))
                              else "") & Label_Append (Buf);

         when N_Simple_Return_Statement | N_Extended_Return_Statement =>
            Buf := "return" & Label_Append (Buf);

         when N_Exit_Statement =>
            Buf := "exit" & (if Name (Node_It) /= Empty then
                                "_" & Get_Name_String (Chars (Name (Node_It)))
                             else "")
              & Label_Append (Buf);

         when others =>
            null;

         end case;

         Node_It := Parent (Node_It);
      end loop;

      if To_String (Buf) /= "" then
         return NID (GP_Prefix & To_String (Buf));
      else
         return No_Name;
      end if;
   end New_Shape_Label;

   -------------------------
   --  New_Comment_Label  --
   -------------------------

   function New_Comment_Label
     (Node : Node_Id; Loc : Name_Id; Reason : VC_Kind) return Name_Id is
      Prefix : constant String := "comment:";
      Str_Loc : constant String := Get_Name_String (Loc);

      Pointer : Source_Ptr := Original_Location (Sloc (Node));
      Src_Buff : constant Source_Buffer_Ptr :=
        Source_Text (Get_Source_File_Index (Pointer));

      Buf : Unbounded_String := Null_Unbounded_String;

      Line : Natural;
      Column : Natural;

      procedure Read_Loc_Label (Line : out Natural; Column : out Natural);

      procedure Read_Loc_Label (Line : out Natural; Column : out Natural) is
         Delim_Start : Natural :=
           Ada.Strings.Fixed.Index (Str_Loc, ":",
                                    Ada.Strings.Fixed.Index
                                      (Str_Loc, ":", Str_Loc'First) + 1) + 1;
         Delim_End : Natural;
      begin
         Delim_End := Ada.Strings.Fixed.Index (Str_Loc, ":", Delim_Start);

         Line := Natural'Value (Str_Loc (Delim_Start .. Delim_End - 1));

         Delim_Start := Delim_End + 1;
         Delim_End := Ada.Strings.Fixed.Index (Str_Loc, ":", Delim_Start);
         Delim_End := (if Delim_End /= 0 then Delim_End - 1 else Str_Loc'Last);

         Column := Natural'Value (Str_Loc (Delim_Start .. Delim_End));
      end Read_Loc_Label;

   begin
      Read_Loc_Label (Line, Column);
      Pointer := Line_Start (Physical_Line_Number (Line),
                             Get_Source_File_Index (Pointer));

      while Src_Buff (Pointer) /= ASCII.LF and Src_Buff (Pointer) /= ASCII.CR
      loop

         Buf := Buf & (if Src_Buff (Pointer) = ASCII.Back_Slash then
                          ASCII.Back_Slash & ASCII.Back_Slash
                       else Src_Buff (Pointer) & "");
         Pointer := Pointer + 1;
      end loop;

      Buf := Buf & ASCII.LF;
      Buf := Buf & (1 .. Column - 1 => ' ') & "^ "
        & Str_Loc (9 .. Str_Loc'Last) & ':' & VC_Kind'Image (Reason);
      return NID (Prefix & To_String (Buf));
   end New_Comment_Label;

   -----------------
   -- New_Or_Expr --
   -----------------

   function New_Or_Expr
     (Left, Right : W_Expr_Id;
      Domain      : EW_Domain) return W_Expr_Id is
   begin
      if Is_False_Boolean (Left) then
         return Right;

      elsif Is_False_Boolean (Right) then
         return Left;

      elsif Domain = EW_Pred then
         return New_Connection (Op     => EW_Or,
                                Left   => +Left,
                                Right  => +Right,
                                Domain => Domain);
      else
         return New_Call (Domain => Domain,
                          Name   => To_Ident (WNE_Bool_Or),
                          Args   => (1 => +Left, 2 => +Right),
                          Typ    => EW_Bool_Type);
      end if;
   end New_Or_Expr;

   function New_Or_Expr
     (Conjuncts : W_Expr_Array;
      Domain    : EW_Domain) return W_Expr_Id is
   begin
      if Conjuncts'Length = 0 then
         return +True_Pred;

      elsif Conjuncts'Length = 1 then
         return Conjuncts (Conjuncts'First);

      elsif Domain = EW_Pred then
         return New_Connection
           (Domain     => Domain,
            Op         => EW_Or,
            Left       => +Conjuncts (Conjuncts'First),
            Right      => +Conjuncts (Conjuncts'First + 1),
            More_Right => Conjuncts (Conjuncts'First + 2 .. Conjuncts'Last));

      else
         declare
            Result : W_Expr_Id :=
              New_Call (Domain => Domain,
                        Name   => To_Ident (WNE_Bool_Or),
                        Args   => (1 => +Conjuncts (Conjuncts'First),
                                   2 => +Conjuncts (Conjuncts'First + 1)));
         begin
            for K in Conjuncts'First + 2 .. Conjuncts'Last loop
               Result := New_Call (Domain => Domain,
                                   Name   => To_Ident (WNE_Bool_Or),
                                   Args   => (1 => Result,
                                              2 => +Conjuncts (K)),
                                   Typ    => EW_Bool_Type);
            end loop;

            return Result;
         end;
      end if;
   end New_Or_Expr;

   function New_Or_Expr
      (Left, Right : W_Expr_Id;
       Domain      : EW_Domain;
       Base        : W_Type_Id) return W_Expr_Id is
   begin
      if Base = EW_Bool_Type then
         return New_Or_Expr (Left, Right, Domain);
      else
         return
           New_Call (Domain => Domain,
                     Name   => Integer_Bitwise_Or,
                     Args   => (1 => +Left, 2 => +Right),
                     Typ    => EW_Int_Type);
      end if;
   end New_Or_Expr;

   ----------------------
   -- New_Or_Else_Expr --
   ----------------------

   function New_Or_Else_Expr
     (Left, Right : W_Expr_Id;
      Domain      : EW_Domain) return W_Expr_Id
   is
   begin
      if Is_False_Boolean (Left) then
         return Right;
      elsif Is_False_Boolean (Right) then
         return Left;
      else
         if Domain = EW_Prog then
            return
              New_Connection
                (Domain => Domain,
                 Op     => EW_Or_Else,
                 Left   => Left,
                 Right  => Right);
         else
            return New_Or_Expr (Left, Right, Domain);
         end if;
      end if;
   end New_Or_Else_Expr;

   -----------------------
   -- New_Sub_VC_Marker --
   -----------------------

   function New_Sub_VC_Marker (N : Node_Id) return Name_Id
   is
      Used_Node : Node_Id := N;
   begin

      --  String_Of_Node almost systematically prints the original node of the
      --  argument node. This is usually what we want, except in one strange
      --  case: The frontend rewrites N_And_Then Chains to lists of simple
      --  expressions, but the original node of each points to the N_And_Then,
      --  instead of the expression itself. We work around this by getting the
      --  right op of the original node in that case.

      --  ??? fix String_Of_Node instead of this workaround

      if Comes_From_Source (N) and then Original_Node (N) /= N and then
        Nkind (Original_Node (N)) = N_And_Then
      then
         Used_Node := Right_Opnd (Original_Node (N));
      end if;

      return NID (Pretty_Ada_Tag & ":" & Int_Image (Integer (Used_Node)));
   end New_Sub_VC_Marker;

   --------------------
   -- New_Range_Expr --
   --------------------

   function New_Range_Expr
     (Domain    : EW_Domain;
      Low, High : W_Expr_Id;
      Expr      : W_Expr_Id) return W_Expr_Id
   is
   begin
      return
         New_And_Expr
           (Left  =>
              New_Comparison
                (Domain    => Domain,
                 Cmp       => EW_Le,
                 Left      => Low,
                 Right     => Expr),
            Right  =>
              New_Comparison
                (Domain    => Domain,
                 Cmp       => EW_Le,
                 Left      => Expr,
                 Right     => High),
            Domain => Domain);
   end New_Range_Expr;

   ---------------------------
   -- New_Simpl_Conditional --
   ---------------------------

   function New_Simpl_Conditional
      (Condition : W_Expr_Id;
       Then_Part : W_Expr_Id;
       Else_Part : W_Expr_Id;
       Domain    : EW_Domain) return W_Expr_Id
   is
   begin
      if Is_True_Boolean (Condition) then
         return Then_Part;
      elsif Is_False_Boolean (Condition) then
         return Else_Part;
      else
         return
           New_Conditional
             (Condition => +Condition,
              Then_Part => Then_Part,
              Else_Part => Else_Part,
              Domain    => Domain,
              Typ       => Get_Type (Then_Part));
      end if;
   end New_Simpl_Conditional;

   -----------------------
   -- New_Temp_For_Expr --
   -----------------------

   function New_Temp_For_Expr
     (E         : W_Expr_Id;
      Need_Temp : Boolean := True)
      return W_Expr_Id
   is
   begin

      --  Internally, we use a map to store the expression for which we
      --  introduce a temporary variable. The map holds entries:
      --    Identifier -> Expr
      --  It allows us (in Binding_For_Temp) to get the expression for the temp
      --
      --  When it is not actually necessary to generate a temp for Expr, we
      --  do not introduce any binding in the map. We used to generate a
      --  binding Expr => Empty to distinguish (in Binding_For_Temp)
      --  between incorrect usage of the API and a value for which no temp was
      --  necessary. We do not anymore as we could not know how many times
      --  New_Temp_For_Expr had been called for Expr and so how long we should
      --  keep Expr => Empty in the table.

      if Need_Temp
        and then Get_Kind (+E) not in W_Identifier | W_Deref
      then
         declare
            Tmp : constant W_Expr_Id :=
              +New_Temp_Identifier (Ada_Node => Get_Ada_Node (+E),
                                    Typ      => Get_Type (E));
         begin
            Temp_Names_Map.Insert (+Tmp, +E);
            return Tmp;
         end;
      else
         return E;
      end if;
   end New_Temp_For_Expr;

   -----------------------
   -- New_Typed_Binding --
   -----------------------

   function New_Typed_Binding
     (Ada_Node : Node_Id := Empty;
      Domain   : EW_Domain;
      Name     : W_Identifier_Id;
      Def      : W_Expr_Id;
      Context  : W_Expr_Id)
      return W_Expr_Id is
   begin
      return
        New_Binding
          (Ada_Node, Domain, Name, Def, Context, Get_Type (Context));
   end New_Typed_Binding;

   -----------------
   -- New_VC_Call --
   -----------------

   function New_VC_Call
      (Ada_Node : Node_Id;
       Name     : W_Identifier_Id;
       Progs    : W_Expr_Array;
       Reason   : VC_Kind;
       Domain   : EW_Domain;
       Typ      : W_Type_Id) return W_Expr_Id
   is
   begin
      return
        +New_VC_Expr
          (Ada_Node => Ada_Node,
           Reason   => Reason,
           Expr     =>
             New_Call
               (Ada_Node => Ada_Node,
                Name     => Name,
                Args     => Progs,
                Domain   => Domain,
                Typ      => Typ),
           Domain  => Domain);
   end New_VC_Call;

   -----------------
   -- New_VC_Expr --
   -----------------

   function New_VC_Expr
      (Ada_Node : Node_Id;
       Expr     : W_Expr_Id;
       Reason   : VC_Kind;
       Domain   : EW_Domain) return W_Expr_Id
   is
   begin
      if Domain /= EW_Term and then Present (Ada_Node) then
         return
            New_Label
              (Ada_Node => Ada_Node,
               Labels   => New_VC_Labels (Ada_Node, Reason),
               Def      => Expr,
               Domain   => Domain,
               Typ      => Get_Type (Expr));
      else
         return Expr;
      end if;
   end New_VC_Expr;

   -------------------
   -- New_VC_Labels --
   -------------------

   function New_VC_Labels
     (N      : Node_Id;
      Reason : VC_Kind) return Name_Id_Set
   is
      --  A gnatprove label in Why3 has the following form
      --
      --  "GP_Reason:VC_Kind"     - the kind of the VC
      --  "GP_Sloc:file:line:col" - the sloc of the construct that triggers the
      --  VC
      --  "keep_on_simp"          - tag that disallows simplifying this VC away
      --
      --  For a node inside an instantiation, we use the location of the
      --  top-level instantiation. This could be refined in the future.

      Set : Name_Id_Set := Name_Id_Sets.Empty_Set;
      Id  : constant VC_Id := Register_VC (N, Current_Subp);
      Location_Lab : Name_Id;
   begin
      Set.Include (NID ("GP_Reason:" & VC_Kind'Image (Reason)));
      Set.Include (NID ("GP_Id:" & Int_Image (Integer (Id))));

      Location_Lab := New_Located_Label
        (N, Left_Most => Locate_On_First_Token (Reason));
      Set.Include (Location_Lab);
      Set.Include (New_Comment_Label (N, Location_Lab, Reason));
      Set.Include (New_Shape_Label (Node => N));
      Set.Include (NID (Keep_On_Simp));
      return Set;
   end New_VC_Labels;

   ------------------
   -- New_Xor_Expr --
   ------------------

   function New_Xor_Expr
      (Left, Right : W_Expr_Id;
       Domain      : EW_Domain;
       Base        : W_Type_Id) return W_Expr_Id is

   begin
      if Domain = EW_Pred and then Base = EW_Bool_Type then
         declare
            Or_Expr : constant W_Expr_Id := New_Or_Expr (Left, Right, Domain);
            Both_Expr : constant W_Expr_Id :=
              New_And_Expr (Left, Right, Domain);
            Not_Both_Expr : constant W_Expr_Id :=
              New_Not (Domain => Domain, Right => Both_Expr);
         begin
            return New_Connection
              (Domain => Domain,
               Op     => EW_And,
               Left   => Or_Expr,
               Right  => Not_Both_Expr);
         end;
      else
         declare
            Id : constant W_Identifier_Id :=
              (if Base = EW_Bool_Type then To_Ident (WNE_Bool_Xor)
                 else Integer_Bitwise_Xor);
         begin
            return
              New_Call
                (Domain => Domain,
                 Name   => Id,
                 Args   => (1 => +Left, 2 => +Right),
                 Typ    =>
                   (if Base = EW_Bool_Type then EW_Bool_Type
                    else EW_Int_Type));
         end;
      end if;
   end New_Xor_Expr;

   ------------
   -- To_Int --
   ------------

   function To_Int (D : EW_Domain; E : W_Expr_Id) return W_Expr_Id is
   begin
      return
        Insert_Scalar_Conversion (Domain => D, Expr => E, To => EW_Int_Type);
   end To_Int;

   -----------------------
   -- Why_Default_Value --
   -----------------------

   function Why_Default_Value (Domain : EW_Domain;
                               E      : Entity_Id) return W_Expr_Id
   is
      Why_Ent : constant Entity_Id :=
        Get_Ada_Node (+EW_Abstract (E));
   begin
      if Is_Standard_Boolean_Type (E) then
         return New_Literal (Domain => Domain, Value => EW_True);
      else
         return +New_Identifier (Ada_Node => Why_Ent,
                                 Domain  => Domain,
                                 Module  => E_Module (Why_Ent),
                                 Name    => To_String (WNE_Dummy),
                                 Typ     => EW_Abstract (Why_Ent));
      end if;
   end Why_Default_Value;

end Why.Gen.Expr;
