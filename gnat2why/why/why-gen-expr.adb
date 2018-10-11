------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                          W H Y - G E N - E X P R                         --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                       Copyright (C) 2010-2018, AdaCore                   --
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

with Ada.Containers;
with Ada.Containers.Hashed_Maps;
with Ada.Strings;                use Ada.Strings;
with Ada.Strings.Unbounded;      use Ada.Strings.Unbounded;
with Ada.Strings.Fixed;
with Checks;                     use Checks;
with Common_Containers;          use Common_Containers;
with Errout;                     use Errout;
with Eval_Fat;
with Gnat2Why.Error_Messages;    use Gnat2Why.Error_Messages;
with Gnat2Why.Expr;              use Gnat2Why.Expr;
with Gnat2Why.Subprograms;       use Gnat2Why.Subprograms;
with Gnat2Why_Args;
with GNATCOLL.Utils;             use GNATCOLL.Utils;
with Sinput;                     use Sinput;
with SPARK_Atree.Entities;       use SPARK_Atree.Entities;
with SPARK_Util.Subprograms;     use SPARK_Util.Subprograms;
with SPARK_Util.Types;           use SPARK_Util.Types;
with Stand;                      use Stand;
with Urealp;                     use Urealp;
with Why.Atree.Accessors;        use Why.Atree.Accessors;
with Why.Atree.Modules;          use Why.Atree.Modules;
with Why.Atree.Tables;           use Why.Atree.Tables;
with Why.Conversions;            use Why.Conversions;
with Why.Gen.Arrays;             use Why.Gen.Arrays;
with Why.Gen.Binders;            use Why.Gen.Binders;
with Why.Gen.Names;              use Why.Gen.Names;
with Why.Gen.Pointers;           use Why.Gen.Pointers;
with Why.Gen.Preds;              use Why.Gen.Preds;
with Why.Gen.Progs;              use Why.Gen.Progs;
with Why.Gen.Records;            use Why.Gen.Records;
with Why.Gen.Scalars;            use Why.Gen.Scalars;

package body Why.Gen.Expr is

   function Args_For_Scalar_Dynamic_Property
     (Ty     : Entity_Id;
      Expr   : W_Expr_Id;
      Params : Transformation_Params := Body_Params) return W_Expr_Array;
   --  Computes the arguments to be used for a call to the dynamic property
   --  of a scalar type.

   function Insert_Single_Conversion
     (Ada_Node : Node_Id;
      Domain   : EW_Domain;
      To       : W_Type_Id;
      Expr     : W_Expr_Id) return W_Expr_Id;
   --  Assuming that there is at most one step between To and From in the
   --  type hierarchy (i.e. that there exists a conversion from From
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

   function New_Located_Label (Input : Source_Ptr) return Name_Id;
   --  @param Input a source pointer
   --  @return a Why3 label which identifies this source location in Why3

   function Is_Essentially_Void_List (L : Why_Node_List) return Boolean;
   --  @param a list of Why nodes
   --  @return True if all elements of the list are essentially void

   function Compute_VC_Sloc (N         : Node_Id;
                             Left_Most : Boolean := False) return Source_Ptr;
   --  @param N a node where a Check is located
   --  @param Left_Most whether the returned source_pointer should be oriented
   --    at the left_most of the tree rooted in N
   --  @return the source_pointer of node N, taking into account "Left_Most"
   --    argument and other special cases

   function Why_Node_Hash (X : Why_Node_Id) return Ada.Containers.Hash_Type is
     (Ada.Containers.Hash_Type (X));

   package Why_Node_Maps is new Ada.Containers.Hashed_Maps
     (Key_Type        => Why_Node_Id,
      Element_Type    => Why_Node_Id,
      Hash            => Why_Node_Hash,
      Equivalent_Keys => "=");

   Temp_Names_Map : Why_Node_Maps.Map := Why_Node_Maps.Empty_Map;

   --------------------------------------
   -- Args_For_Scalar_Dynamic_Property --
   --------------------------------------

   function Args_For_Scalar_Dynamic_Property
     (Ty     : Entity_Id;
      Expr   : W_Expr_Id;
      Params : Transformation_Params := Body_Params) return W_Expr_Array
   is
   begin
      return (1 => New_Attribute_Expr
                 (Ty     => Ty,
                  Domain => EW_Term,
                  Attr   => Attribute_First,
                  Params => Params),
              2 => New_Attribute_Expr
                   (Ty     => Ty,
                    Domain => EW_Term,
                    Attr   => Attribute_Last,
                    Params => Params),
              3 =>
                Insert_Simple_Conversion
                  (Ada_Node => Ty,
                   Domain   => EW_Term,
                   Expr     => Expr,
                   To       => Base_Why_Type (Ty)));
   end Args_For_Scalar_Dynamic_Property;

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

   ---------------------
   -- Compute_VC_Sloc --
   ---------------------

   function Compute_VC_Sloc (N         : Node_Id;
                             Left_Most : Boolean := False) return Source_Ptr
   is
      Slc : Source_Ptr;
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
           and then Is_Rewrite_Substitution (N)
           and then Nkind (Original_Node (N)) = N_And_Then)
      then
         Slc := Sloc (N);
      else
         Slc := Safe_First_Sloc (N);
      end if;
      return Slc;
   end Compute_VC_Sloc;

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
            return +Get_Typ (W_Fixed_Constant_Id (E));

         when W_Real_Constant =>
            return EW_Real_Type;

         when W_Float_Constant =>
            return +Get_Typ (W_Float_Constant_Id (E));

         when W_Range_Constant =>
            return +Get_Typ (W_Range_Constant_Id (E));

         when W_Modular_Constant =>
            return +Get_Typ (W_Modular_Constant_Id (E));

         when W_Literal =>
            return EW_Bool_Type;

         when W_While_Loop
            | W_Assignment
            | W_Assert
         =>
            return EW_Unit_Type;

         when W_Connection
            | W_Not
            | W_Universal_Quantif
            | W_Existential_Quantif
         =>
            return EW_Bool_Type;

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

         when W_Loc_Label =>
            return Get_Type (Get_Def (W_Loc_Label_Id (E)));

         when W_Epsilon =>
            return Get_Typ (W_Epsilon_Id (E));

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
     (Domain         : EW_Domain;
      Ada_Node       : Node_Id := Empty;
      Expr           : W_Expr_Id;
      To             : W_Type_Id;
      Need_Check     : Boolean := False;
      Force_No_Slide : Boolean := False;
      Is_Qualif      : Boolean := False)
      return W_Expr_Id
   is
      From      : constant W_Type_Id := Get_Type (Expr);
      To_Ent    : constant Entity_Id := Get_Ada_Node (+To);
      From_Ent  : constant Entity_Id := Get_Ada_Node (+From);
      Dim       : constant Positive := Positive (Number_Dimensions (To_Ent));

      function Needs_Slide (From_Ent, To_Ent : Entity_Id) return Boolean;
      --  Check whether a conversion between those types requires sliding.

      function Insert_Array_Index_Check
        (Expr   : W_Expr_Id;
         To_Ent : Entity_Id) return W_Prog_Id;

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
         Check : W_Pred_Id;

      begin
         pragma Assert (not Is_Static_Array_Type (To_Ent));

         --  For dynamic types, use dynamic_property

         Check := +New_Dynamic_Property
           (Domain => EW_Prog,
            Ty     => To_Ent,
            Expr   => Expr);

         return New_Located_Assert (Ada_Node,
                                    Check,
                                    VC_Range_Check,
                                    EW_Assert);
      end Insert_Array_Range_Check;

      ------------------------------
      -- Insert_Array_Index_Check --
      ------------------------------

      function Insert_Array_Index_Check
        (Expr   : W_Expr_Id;
         To_Ent : Entity_Id) return W_Prog_Id
      is
         Check : W_Pred_Id;
         Dim   : constant Positive :=
           Positive (Number_Dimensions (To_Ent));
         Eqs   : W_Expr_Array (1 .. 2 * Dim);
      begin
         for I in 1 .. Dim loop
            Eqs (2 * I - 1) := New_Comparison
              (Symbol => Why_Eq,
               Left   => Get_Array_Attr
                 (Domain => EW_Term,
                  Expr   => Expr,
                  Attr   => Attribute_First,
                  Dim    => I),
               Right  => Get_Array_Attr
                 (Domain => EW_Term,
                  Attr   => Attribute_First,
                  Dim    => I,
                  Ty     => To_Ent),
               Domain => EW_Pred);
            Eqs (2 * I) := New_Comparison
              (Symbol => Why_Eq,
               Left   => Get_Array_Attr
                 (Domain => EW_Term,
                  Expr   => Expr,
                  Attr   => Attribute_Last,
                  Dim    => I),
               Right  => Get_Array_Attr
                 (Domain => EW_Term,
                  Attr   => Attribute_Last,
                  Dim    => I,
                  Ty     => To_Ent),
               Domain => EW_Pred);
         end loop;
         Check := +New_And_Expr (Eqs, EW_Pred);

         return New_Located_Assert (Ada_Node,
                                    Check,
                                    VC_Index_Check,
                                    EW_Assert);
      end Insert_Array_Index_Check;

      -------------------------
      -- Insert_Length_Check --
      -------------------------

      function Insert_Length_Check
        (Expr   : W_Expr_Id;
         To_Ent : Entity_Id) return W_Prog_Id
      is
         Check     : W_Pred_Id := True_Pred;
         Is_Static : constant Boolean := Has_Static_Array_Type (To_Ent)
           and then Has_Static_Array_Type (Get_Ada_Node (+Get_Type (Expr)));

      begin
         for I in 1 .. Dim loop

            --  Do not issue checks for statically matching lengths

            if not Is_Static
              or else Static_Array_Length (Retysp (To_Ent), I) /=
                Static_Array_Length
                  (Retysp (Get_Ada_Node (+Get_Type (Expr))), I)
            then
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
                       New_Call
                         (Name   => Why_Eq,
                          Typ    => EW_Bool_Type,
                          Domain => Domain,
                          Args   => (+Input_Length, +Expected_Length)));
               end;
            end if;
         end loop;

         if Is_True_Boolean (+Check) then
            return +Void;
         else
            return
              New_Located_Assert (Ada_Node, Check, VC_Length_Check, EW_Assert);
         end if;
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
                 Type_Low_Bound (Nth_Index_Type (From_Ent, I));
               Low_To   : constant Node_Id :=
                 Type_Low_Bound (Nth_Index_Type (To_Ent, I));
            begin
               if not Is_Static_Expression (Low_From)
                 or else not Is_Static_Expression (Low_To)
                 or else Expr_Value (Low_From) /= Expr_Value (Low_To)
               then
                  return True;
               end if;
            end;
         end loop;

         --  We statically know that the "first" are actually equal, no sliding
         --  needed

         return False;
      end Needs_Slide;

      Need_Slide : constant Boolean := Needs_Slide (From_Ent, To_Ent);
      Sliding    : constant Boolean :=
        not Force_No_Slide and then Need_Slide and then not Is_Qualif;
      Arr_Expr   : W_Expr_Id;
      T          : W_Expr_Id;
      Pred_Check : constant Boolean :=
        Domain = EW_Prog
        and then Need_Check
        and then Has_Predicates (Get_Ada_Node (+To))
        and then not Is_Call_Arg_To_Predicate_Function (Ada_Node);

   --  Beginning of processing for Insert_Array_Conversion

   begin
      if To_Ent = From_Ent then

         --  In the case of unconstrained arrays, the Ada entity may be equal,
         --  but in Why we have to convert from the split representation to the
         --  unique representation. This is checked here.

         if not Has_Static_Array_Type (To_Ent) then
            if Get_Type_Kind (From) = EW_Split and then
              Get_Type_Kind (To) = EW_Abstract
            then
               return Array_Convert_From_Base (Domain, Expr);
            elsif Get_Type_Kind (From) = EW_Abstract and then
              Get_Type_Kind (To) = EW_Split
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

      --  1 - Put array in split form. If reconstruction is needed, also store
      --  appropriate bounds in Args.

      declare
         Args    : W_Expr_Array (1 .. 1 + 2 * Dim);
         Arg_Ind : Positive := 1;

         To_Is_Abstract      : constant Boolean :=
           not Is_Static_Array_Type (To_Ent)
           and then Get_Type_Kind (To) /= EW_Split;
         Need_Reconstruction : constant Boolean :=
           To_Is_Abstract
           or else (not Is_Static_Array_Type (To_Ent)
                    and then Pred_Check);
         --  Reconstruction is needed if To is in abstract form or if a
         --  predicate check is required.

         Split_To            : constant W_Type_Id :=
           (if not Need_Reconstruction then To
            else EW_Split (To_Ent));

      begin
         --  Insert sliding if needed

         if Sliding then
            declare
               Args    : W_Expr_Array (1 .. 1 + 2 * Dim);
               Arg_Ind : Positive := 1;
            begin
               Add_Map_Arg (Domain, Args, Arr_Expr, Arg_Ind);
               for I in 1 .. Dim loop
                  Add_Attr_Arg
                    (Domain, Args, Arr_Expr,
                     Attribute_First, I, Arg_Ind);
                  Add_Attr_Arg
                    (Domain, Args, To_Ent,
                     Attribute_First, I, Arg_Ind);
               end loop;

               T := New_Call
                 (Domain => Domain,
                  Name   => Get_Array_Theory (From_Ent).Slide,
                  Args   => Args,
                  Typ    => Split_To);
            end;

            --  If reconstruction is needed, fill the Args array.
            --  Here, we must get attributes from the type as the slided
            --  expression has no registered bounds. It is OK since To must
            --  be constrained.

            if Need_Reconstruction then
               Arg_Ind := 1;
               Add_Map_Arg (Domain, Args, T, Arg_Ind);

               for I in 1 .. Dim loop
                  Add_Attr_Arg
                    (Domain, Args, To_Ent,
                     Attribute_First, I, Arg_Ind);
                  Add_Attr_Arg
                    (Domain, Args, To_Ent,
                     Attribute_Last, I, Arg_Ind);
               end loop;
            end if;

         --  If reconstruction is needed, fill the Args array. T is the
         --  first element of Args. It will be Arr_Expr if from is split
         --  and To_Array (Arr_Expr) otherwise.

         elsif Need_Reconstruction then
            Add_Array_Arg (Domain, Args, Arr_Expr, Arg_Ind);
            T := Args (1);

         --  Both are in split form, T is Arr_Expr

         elsif Is_Static_Array_Type (From_Ent)
           or else Get_Type_Kind (From) = EW_Split
         then
            T := Arr_Expr;

         --  To is in split form but not From. Split From.

         else
            T :=
              New_Call
                (Domain => Domain,
                 Name   => E_Symb (From_Ent, WNE_To_Array),
                 Args   => (1 => Arr_Expr),
                 Typ    => To);
         end if;

         --  2. To_Ent and From_Ent do not have the same component type, apply
         --  the appropriate conversion.

         if Retysp (Component_Type (To_Ent)) /=
           Retysp (Component_Type (From_Ent))
         then
            T := Insert_Single_Conversion
              (Ada_Node => Empty,
               Domain   => Domain,
               To       => Split_To,
               Expr     => T);

         --  No actual why call or conversion may have been inserted, but we
         --  still need to change the type of the Why AST node. We do that by
         --  adding a dummy node.

         else
            T := New_Label (Labels => Name_Id_Sets.Empty_Set,
                            Def    => T,
                            Domain => Domain,
                            Typ    => Split_To);
         end if;

         --  3. Reconstruct the array if needed

         if To_Is_Abstract then
            Args (1) := T;
            T :=
              New_Call
                (Domain => Domain,
                 Name   => E_Symb (To_Ent, WNE_Of_Array),
                 Args   => Args,
                 Typ    => To);
         end if;

         --  4. Insert length, range, index, and predicate check when necessary

         if Domain = EW_Prog and then Need_Check then
            declare
               Check_Type : constant Entity_Id := Get_Ada_Node (+To);
            begin
               if Is_Qualif and then Need_Slide then
                  T := +Sequence
                    (Insert_Array_Index_Check (Arr_Expr, Check_Type),
                     +T);
               elsif Is_Constrained (Check_Type) then
                  T := +Sequence
                    (Insert_Length_Check (Arr_Expr, Check_Type),
                     +T);
               else
                  T := +Sequence
                    (Insert_Array_Range_Check (Arr_Expr, Check_Type),
                     +T);
               end if;

               --  If the target type has a direct or inherited predicate,
               --  generate a corresponding check. Do not generate a predicate
               --  check for an internal call to a parent predicate function
               --  inside the definition of a predicate function.

               if Pred_Check then
                  declare
                     W_Tmp   : constant W_Identifier_Id :=
                       New_Temp_Identifier (Typ => Get_Type (+T));
                     Do_Rec  : constant Boolean :=
                       not Is_Static_Array_Type (To_Ent)
                       and then Get_Type_Kind (To) = EW_Split;
                     Rec_Tmp : constant W_Expr_Id :=
                       (if Do_Rec then
                           New_Call
                          (Domain => Domain,
                           Name   => E_Symb (To_Ent, WNE_Of_Array),
                           Args   => Args,
                           Typ    => EW_Abstract (To_Ent))
                        else +W_Tmp);
                     --  If it is in split form, the array should be
                     --  reconstructed.

                     W_Seq  : W_Prog_Id;
                  begin
                     Args (1) := +W_Tmp;

                     W_Seq := Sequence
                       (New_Predicate_Check (Ada_Node, Check_Type, Rec_Tmp),
                        +W_Tmp);

                     T := +W_Expr_Id'(New_Binding
                                      (Ada_Node => Ada_Node,
                                       Domain   => EW_Prog,
                                       Name     => W_Tmp,
                                       Def      => T,
                                       Context  => +W_Seq,
                                       Typ      => Get_Type (+T)));
                  end;
               end if;
            end;
         end if;
      end;

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
      Domain   : EW_Domain;
      Expr     : W_Expr_Id;
      To       : W_Type_Id;
      Lvalue   : Boolean := False) return W_Expr_Id
   is

      --  When converting between Ada types, detect cases where a check is not
      --  needed.

      From          : constant W_Type_Id := Get_Type (Expr);
      Check_Needed  : Boolean;
      T : W_Expr_Id := Expr;

   begin

      if not Need_Conversion (Expr) then
         return Expr;
      end if;

      --  A string literal gets typed with a subtype of the expected type, even
      --  if it does not respect the associated predicate of the expected type.
      --  As a result, do not rely on the call to Check_Needed_On_Conversion in
      --  that case.

      Check_Needed :=
        (if Get_Type_Kind (From) in EW_Abstract | EW_Split
           and then Get_Type_Kind (To) in EW_Abstract | EW_Split
           and then not (Nkind (Ada_Node) = N_String_Literal
                          and then Has_Predicates (Get_Ada_Node (+To)))
         then
            Check_Needed_On_Conversion (From => Get_Ada_Node (+From),
                                        To   => Get_Ada_Node (+To))
         or else
            Is_Choice_Of_Unconstrained_Array_Update (Ada_Node)
         else
            True);

      if Is_Private_Conversion (From, To)
        or else Is_Record_Conversion (From, To)
      then
         --  Conversion between record types need to go through their common
         --  root record type. A discriminant check may be needed. Currently
         --  perform it on all discriminant record types, as the flag
         --  Do_Discriminant_Check is not set appropriately by the frontend on
         --  type conversions.
         --  A tag check may also be needed if we convert from a classwide type
         --  to a type which is not an ancestor. As for the discriminant check,
         --  we always perform it.

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

      elsif Is_Pointer_Conversion (From, To) then
         --  ??? [R525-018]
         --     type L_Ptr is access L;
         --     L1 : L_Ptr := new L(14);
         --     L2 : L_Ptr := new L(26);
         --     L1 := L2

         T := Insert_Pointer_Conversion (Domain     => Domain,
                                         Ada_Node   => Ada_Node,
                                         Expr       => T,
                                         To         => To,
                                         Need_Check => Check_Needed);

      --  Conversion between scalar types

      else
         declare
            --  Flag for a range check; set if the expression node has
            --  Do_Range_Check flag set, if it is a type conversion whose flag
            --  Do_Overflow_Check is set. (See description of these flags in
            --  sinfo.ads for details.)

            --  Also, we special case a type conversion whose expression has a
            --  range check, when this appears as the actual of an out/in-out
            --  parameter of a call, because the current check machinery does
            --  not allow detecting the necessary check on the out copy.
            --  ??? It would be good if such special casing were closer to the
            --  code which handles the call

            Do_Check : constant Boolean :=
              Domain = EW_Prog and then Check_Needed and then
              Do_Check_On_Scalar_Converion (Ada_Node);

         begin
            T := Insert_Scalar_Conversion (Domain   => Domain,
                                           Ada_Node => Ada_Node,
                                           Expr     => T,
                                           To       => To,
                                           Do_Check => Do_Check,
                                           Lvalue   => Lvalue);
         end;
      end if;

      return T;
   end Insert_Checked_Conversion;

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
      From   : constant W_Type_Id := Get_Type (Expr);
      --  Current result expression
      Result : W_Expr_Id := Expr;

      L : constant Node_Id := Get_Ada_Node (+From);
      R : constant Node_Id := Get_Ada_Node (+To);
      pragma Assert (Root_Record_Type (L) = Root_Record_Type (R));

      Need_Conv : constant Boolean :=
        Oldest_Parent_With_Same_Fields (L) /=
        Oldest_Parent_With_Same_Fields (R);

      Base : constant W_Type_Id := EW_Abstract (Root_Record_Type (L));

      Need_Discr_Check : constant Boolean :=
        Need_Check and then Count_Discriminants (R) > 0
        and then Is_Constrained (R);
      Need_Tag_Check   : constant Boolean :=
        Need_Check and then Is_Tagged_Type (R) and then not Is_Ancestor (R, L);

      --  Do not generate a predicate check for an internal call to a parent
      --  predicate function inside the definition of a predicate function.
      Need_Pred_Check : constant Boolean :=
        Need_Check
          and then Has_Predicates (R)
          and then not Is_Call_Arg_To_Predicate_Function (Ada_Node);
      Check_Entity    : constant Entity_Id := Get_Ada_Node (+To);

   begin
      --  When From = To and no check needs to be inserted, do nothing

      if not Need_Conv and then not Need_Check then
         return Expr;
      end if;

      --  1. Convert From -> Base

      Result := Insert_Single_Conversion (Domain   => Domain,
                                          Ada_Node => Ada_Node,
                                          To       => Base,
                                          Expr     => Result);

      --  2. Possibly perform checks on root type

      if Domain = EW_Prog then

         --  2.a Possibly perform a discriminant check

         if Need_Discr_Check then
            Result := +Insert_Subtype_Discriminant_Check (Ada_Node,
                                                          Check_Entity,
                                                          +Result);
         end if;

         --  2.b Possibly perform a tag check

         if Need_Tag_Check then
            Result := +Insert_Tag_Check (Ada_Node,
                                         Check_Entity,
                                         +Result);
         end if;
      end if;

      --  3. Convert Base -> To

      Result := Insert_Single_Conversion (Domain   => Domain,
                                          Ada_Node => Ada_Node,
                                          To       => To,
                                          Expr     => Result);

      --  4. Possibly perform a predicate check on target type To

      if Domain = EW_Prog
        and then Need_Pred_Check
      then
         Result := +Insert_Predicate_Check (Ada_Node,
                                            Check_Entity,
                                            +Result);
      end if;

      return Result;
   end Insert_Record_Conversion;

   -------------------------------
   -- Insert_Pointer_Conversion --
   -------------------------------

   function Insert_Pointer_Conversion
     (Ada_Node   : Node_Id;
      Domain     : EW_Domain;
      Expr       : W_Expr_Id;
      To         : W_Type_Id;
      Need_Check : Boolean := False) return W_Expr_Id
   is
      From   : constant W_Type_Id := Get_Type (Expr);
      --  Current result expression
      Result : W_Expr_Id := Expr;

      L : constant Node_Id := Get_Ada_Node (+From);
      R : constant Node_Id := Get_Ada_Node (+To);

      pragma Assert (Root_Pointer_Type (L) = Root_Pointer_Type (R));

      Des_Typ : constant Node_Id := Directly_Designated_Type (R);

      Need_Discr_Check : constant Boolean :=
        Need_Check and then Count_Discriminants (Des_Typ) > 0
        and then Is_Constrained (Des_Typ);

      Need_Not_Null_Check : constant Boolean := Can_Never_Be_Null (R);

      --  Do not generate a predicate check for an internal call to a parent
      --  predicate function inside the definition of a predicate function.

      Need_Pred_Check : constant Boolean :=
        Has_Predicates (R)
        and then not Is_Call_Arg_To_Predicate_Function (Ada_Node);

      Check_Entity : constant Entity_Id := Get_Ada_Node (+To);

   begin
      --  When no check needs to be inserted, do nothing
      --  ??? should test on From = To before and then Need_Check

      if not Need_Check then
         return Expr;
      end if;

      if Domain = EW_Prog then

         --  Possibly perform a discriminant check

         if Need_Discr_Check then
            Result := +Insert_Subtype_Discriminant_Check (Ada_Node,
                                                          Check_Entity,
                                                          +Result);
         end if;

         if Need_Pred_Check then
            Result := +Insert_Predicate_Check (Ada_Node,
                                               Check_Entity,
                                               +Result);
         end if;

         if Need_Not_Null_Check then
            Result :=
              +New_VC_Call
              (Ada_Node => Ada_Node,
               Name     => To_Program_Space
                 (E_Symb (R, WNE_Assign_Null_Check)),
               Progs    => (1 => +Result),
               Domain   => EW_Prog,
               Reason   => VC_Null_Exclusion,
               Typ      => Get_Type (+Expr));
         end if;

      end if;

      return Result;
   end Insert_Pointer_Conversion;

   --------------------------
   -- Insert_Cnt_Loc_Label --
   --------------------------

   function Insert_Cnt_Loc_Label
     (Ada_Node : Node_Id;
      E        : W_Expr_Id) return W_Expr_Id
   is
   begin
      if Present (Ada_Node)
        and then Safe_First_Sloc (Ada_Node) > No_Location
      then
         return New_Loc_Label
           (Ada_Node => Get_Ada_Node (+E),
            Sloc     => Safe_First_Sloc (Ada_Node),
            Domain   => Get_Domain (+E),
            Def      => E);
      else
         return E;
      end if;
   end Insert_Cnt_Loc_Label;

   --------------------------------------
   -- Insert_Conversion_To_Rep_No_Bool --
   --------------------------------------

   function Insert_Conversion_To_Rep_No_Bool
     (Domain : EW_Domain;
      Expr : W_Expr_Id)
      return W_Expr_Id
   is
      Rep_Typ : constant W_Type_Id := Base_Why_Type_No_Bool (Expr);
   begin
      return Insert_Simple_Conversion (Domain => Domain,
                                       Expr   => Expr,
                                       To     => Rep_Typ);
   end Insert_Conversion_To_Rep_No_Bool;

   --------------------
   -- Do_Index_Check --
   --------------------

   function Do_Index_Check
     (Ada_Node : Node_Id;
      Arr_Expr : W_Expr_Id;
      W_Expr   : W_Expr_Id;
      Dim      : Positive) return W_Prog_Id
   is
      Tmp        : constant W_Expr_Id :=
        New_Temp_For_Expr (W_Expr);
      First_Expr : constant W_Expr_Id :=
        Insert_Conversion_To_Rep_No_Bool (Domain => EW_Term,
                                          Expr   => Get_Array_Attr
                                            (Domain => EW_Term,
                                             Expr   => Arr_Expr,
                                             Attr   => Attribute_First,
                                             Dim    => Dim));
      Last_Expr  : constant W_Expr_Id :=
        Insert_Conversion_To_Rep_No_Bool (Domain => EW_Term,
                                          Expr   => Get_Array_Attr
                                            (Domain => EW_Term,
                                             Expr   => Arr_Expr,
                                             Attr   => Attribute_Last,
                                             Dim    => Dim));
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
      Check_Kind : Scalar_Check_Kind) return W_Prog_Id
   is
      W_Type : constant W_Type_Id :=
        (if Get_Type_Kind (Get_Type (W_Expr)) = EW_Split
         then Base_Why_Type (Get_Ada_Node (+Get_Type (W_Expr)))
         else Get_Type (W_Expr));
      Result : W_Prog_Id;
      W_Fun  : W_Identifier_Id;  --  range checking function

   begin
      --  When the range check comes from a modular type, either the expression
      --  is a bitvector and we apply the check on the largest bitvector type
      --  involved, or the expression is an int and we need to apply the check
      --  on int, as we don't know that the value of the expression fits in a
      --  bitvector.

      if Is_Modular_Integer_Type (Ty) then

         --  The type of expression is int, so we apply the range check on int

         if W_Type = EW_Int_Type then

            W_Fun := E_Symb (Ty, WNE_Range_Check_Fun_BV_Int);

            --  If the bounds are dynamic, we need to retrieve them for the
            --  check.

            if Type_Is_Modeled_As_Base (Ty) then
               declare
                  --  Convert first and last bounds from bitvector to int
                  W_First : constant W_Expr_Id :=
                    Insert_Simple_Conversion
                      (Ada_Node => Ty,
                       Domain   => EW_Term,
                       Expr     =>
                         New_Attribute_Expr (Ty     => Ty,
                                             Domain => EW_Term,
                                             Attr   => Attribute_First,
                                             Params => Body_Params),
                       To       => EW_Int_Type);
                  W_Last : constant W_Expr_Id :=
                    Insert_Simple_Conversion
                      (Ada_Node => Ty,
                       Domain   => EW_Term,
                       Expr     =>
                         New_Attribute_Expr (Ty     => Ty,
                                             Domain => EW_Term,
                                             Attr   => Attribute_Last,
                                             Params => Body_Params),
                       To       => EW_Int_Type);

                  --  Range check on int returns an int. To avoid converting it
                  --  back to bitvector which is harder for automatic provers,
                  --  save the bitvector value in a temporary to return later.
                  W_Tmp     : constant W_Expr_Id := New_Temp_For_Expr (W_Expr);
                  W_Int_Tmp : constant W_Expr_Id :=
                    Insert_Simple_Conversion (Ada_Node => Ty,
                                              Domain   => EW_Term,
                                              Expr     => W_Tmp,
                                              To       => EW_Int_Type);
               begin
                  Result :=
                    +New_VC_Call (Domain   => EW_Prog,
                                  Ada_Node => Ada_Node,
                                  Name     => W_Fun,
                                  Progs    => (1 => W_First,
                                               2 => W_Last,
                                               3 => W_Int_Tmp),
                                  Reason   => To_VC_Kind (Check_Kind),
                                  Typ      => Get_Type (W_Expr));
                  Result :=
                    +Binding_For_Temp (Domain  => EW_Prog,
                                       Tmp     => W_Tmp,
                                       Context => +Sequence (Result, +W_Tmp));
               end;

            --  If the bounds are static, the range checking function knows
            --  them, simply call it.

            else
               Result := +New_VC_Call (Domain   => EW_Prog,
                                       Ada_Node => Ada_Node,
                                       Name     => W_Fun,
                                       Progs    => (1 => +W_Expr),
                                       Reason   => To_VC_Kind (Check_Kind),
                                       Typ      => Get_Type (W_Expr));
            end if;

         elsif Why_Type_Is_Float (W_Type) then

            --  In the case of a convertion of a float into a bitvector, we
            --  perform the range check with floats by converting the bounds
            --  of the bitvector range into float and rounding W_Expr to the
            --  nearest integer (RNA). For this to be correct the first element
            --  of the range needs to be converted towards +infinity (RTP) and
            --  the last element towards -infinity (RTN).

            W_Fun := MF_Floats (W_Type).Range_Check;

            declare
               BV_Size : constant Uint := Modular_Size (Ty);

               Of_BV_RTP : constant W_Identifier_Id :=
                 (if BV_Size = Uint_8 then
                     MF_Floats (W_Type).Of_BV8_RTP
                  elsif BV_Size = Uint_16 then
                     MF_Floats (W_Type).Of_BV16_RTP
                  elsif BV_Size = Uint_32 then
                     MF_Floats (W_Type).Of_BV32_RTP
                  elsif BV_Size = Uint_64 then
                     MF_Floats (W_Type).Of_BV64_RTP
                  else
                     raise Program_Error);

               Of_BV_RTN : constant W_Identifier_Id :=
                 (if BV_Size = Uint_8 then
                     MF_Floats (W_Type).Of_BV8_RTN
                  elsif BV_Size = Uint_16 then
                     MF_Floats (W_Type).Of_BV16_RTN
                  elsif BV_Size = Uint_32 then
                     MF_Floats (W_Type).Of_BV32_RTN
                  elsif BV_Size = Uint_64 then
                     MF_Floats (W_Type).Of_BV64_RTN
                  else
                     raise Program_Error);

               --  Convert first and last bounds from bitvector to float
               W_First : constant W_Expr_Id :=
                 New_Call (Domain => EW_Term,
                           Name   => Of_BV_RTP,
                           Args   =>
                             (1 => New_Attribute_Expr
                                  (Ty     => Ty,
                                   Domain => EW_Term,
                                   Attr   => Attribute_First,
                                   Params => Body_Params)),
                           Typ => W_Type);

               W_Last : constant W_Expr_Id :=
                 New_Call (Domain => EW_Term,
                           Name   => Of_BV_RTN,
                           Args   =>
                             (1 => New_Attribute_Expr
                                  (Ty     => Ty,
                                   Domain => EW_Term,
                                   Attr   => Attribute_Last,
                                   Params => Body_Params)),
                           Typ    => W_Type);

               W_Expr_Rounded : constant W_Expr_Id :=
                 New_Call (Domain => EW_Term,
                           Name   => MF_Floats (W_Type).Rounding,
                           Args   => (1 => W_Expr),
                           Typ    => W_Type);
            begin
               Result :=
                 +New_VC_Call (Domain   => EW_Prog,
                               Ada_Node => Ada_Node,
                               Name     => W_Fun,
                               Progs    => (1 => W_First,
                                            2 => W_Last,
                                            3 => W_Expr_Rounded),
                               Reason   => To_VC_Kind (Check_Kind),
                               Typ      => Get_Type (W_Expr));
            end;

         --  The type of expression is bitvector, so we apply the range check
         --  on the largest bitvector type involved.
         else
            pragma Assert (Why_Type_Is_BitVector (W_Type));

            W_Fun := Range_Check_Name (Ty, Check_Kind);

            --  If the bounds are dynamic, we need to retrieve them for the
            --  check, by calling Args_For_Scalar_Dynamic_Property.

            if Type_Is_Modeled_As_Base (Ty) then
               declare
                  W_Tmp  : constant W_Expr_Id := New_Temp_For_Expr (W_Expr);
                  W_Args : constant W_Expr_Array :=
                    Args_For_Scalar_Dynamic_Property (Ty, W_Tmp);
               begin
                  Result :=
                    +New_VC_Call (Domain   => EW_Prog,
                                  Ada_Node => Ada_Node,
                                  Name     => W_Fun,
                                  Progs    => W_Args,
                                  Reason   => To_VC_Kind (Check_Kind),
                                  Typ      => Get_Type (W_Expr));
                  Result :=
                    +Binding_For_Temp (Domain  => EW_Prog,
                                       Tmp     => W_Tmp,
                                       Context => +Sequence (Result, +W_Tmp));
               end;

            --  If the bounds are static, the range checking function knows
            --  them.

            --  When converting from a bitvector of a smaller size, the
            --  expression can be safely converted to the target bitvector
            --  and the range check performed in the target bitvector, we then
            --  convert back to W_Type.

            elsif BitVector_Type_Size (W_Type) <= Modular_Size (Ty) then
               declare
                  Range_Typ : constant W_Type_Id := Type_Of_Node (Ty);
               begin
                  Result := +Insert_Simple_Conversion
                    (Domain => EW_Prog,
                     Expr   =>
                       New_VC_Call (Domain   => EW_Prog,
                                    Ada_Node => Ada_Node,
                                    Name     => W_Fun,
                                    Progs    =>
                                      (1 => +Insert_Simple_Conversion
                                           (Domain => EW_Prog,
                                            Expr   => W_Expr,
                                            To     => Range_Typ)),
                                    Reason   => To_VC_Kind (Check_Kind),
                                    Typ      => Range_Typ),
                     To     => W_Type);
               end;

            --  When converting to a bitvector of a stricly smaller size, the
            --  range check must be performed on the expression before it is
            --  converted to the target bitvector. Instead, convert the bounds
            --  of the target type to the larger source bitvector.

            else
               declare
                  W_First : constant W_Expr_Id :=
                    Insert_Simple_Conversion
                      (Domain   => EW_Term,
                       Expr     =>
                         New_Attribute_Expr (Ty     => Ty,
                                             Domain => EW_Prog,
                                             Attr   => Attribute_First,
                                             Params => Body_Params),
                       To       => W_Type);
                  W_Last : constant W_Expr_Id :=
                    Insert_Simple_Conversion
                      (Domain   => EW_Term,
                       Expr     =>
                         New_Attribute_Expr (Ty     => Ty,
                                             Domain => EW_Prog,
                                             Attr   => Attribute_Last,
                                             Params => Body_Params),
                       To       => W_Type);
               begin
                  W_Fun := Get_Modular_Converter_Range_Check
                             (W_Type, Base_Why_Type (Ty));
                  Result := +New_VC_Call (Domain   => EW_Prog,
                                          Ada_Node => Ada_Node,
                                          Name     => W_Fun,
                                          Progs    => (1 => W_First,
                                                       2 => W_Last,
                                                       3 => +W_Expr),
                                          Reason   => To_VC_Kind (Check_Kind),
                                          Typ      => W_Type);
               end;
            end if;
         end if;

      --  Range check does not come from a modular type. Everything is done in
      --  the representation type, either int for scalar and fixed-point types
      --  or real for floating-point types.

      else
         W_Fun := Range_Check_Name (Ty, Check_Kind);

         --  If the bounds are dynamic, we need to retrieve them for the check,
         --  by calling Args_For_Scalar_Dynamic_Property.

         if Type_Is_Modeled_As_Base (Ty) then
            declare
               W_Tmp : constant W_Expr_Id := New_Temp_For_Expr (W_Expr);
               W_Args : constant W_Expr_Array :=
                 Args_For_Scalar_Dynamic_Property (Ty, W_Tmp);
            begin
               Result := +New_VC_Call (Domain   => EW_Prog,
                                       Ada_Node => Ada_Node,
                                       Name     => W_Fun,
                                       Progs    => W_Args,
                                       Reason   => To_VC_Kind (Check_Kind),
                                       Typ      => Get_Type (W_Expr));
               Result :=
                 +Binding_For_Temp (Domain  => EW_Prog,
                                    Tmp     => W_Tmp,
                                    Context => +Sequence (Result, +W_Tmp));
            end;

         --  If the bounds are static, the range checking function knows them

         else
            Result := +New_VC_Call (Domain   => EW_Prog,
                                    Ada_Node => Ada_Node,
                                    Name     => W_Fun,
                                    Progs    => (1 => +W_Expr),
                                    Reason   => To_VC_Kind (Check_Kind),
                                    Typ      => Get_Type (W_Expr));
         end if;
      end if;

      return Result;
   end Do_Range_Check;

   ------------------------------
   -- Insert_Scalar_Conversion --
   ------------------------------

   function Insert_Scalar_Conversion
     (Domain   : EW_Domain;
      Ada_Node : Node_Id := Empty;
      Expr     : W_Expr_Id;
      To       : W_Type_Id;
      Do_Check : Boolean := False;
      Lvalue   : Boolean := False) return W_Expr_Id
   is
      From : constant W_Type_Id := Get_Type (Expr);

      --  Do not generate a predicate check for an internal call to a parent
      --  predicate function inside the definition of a predicate function.
      Do_Predicate_Check : constant Boolean :=
        Present (Get_Ada_Node (+To))
          and then Has_Predicates (Get_Ada_Node (+To))
          and then Get_Ada_Node (+To) /= Get_Ada_Node (+From)
          and then not Is_Call_Arg_To_Predicate_Function (Ada_Node);

      --  Type and kind for the range check
      Range_Type : Entity_Id := Empty;
      Check_Kind : Scalar_Check_Kind := RCK_Range;

   --  Start of processing for Insert_Scalar_Conversion

   begin
      --  Do nothing when
      --  1. From = To, and
      --  2. no rounding needed, and
      --  3. no predicate check needed, and
      --  4. a) no range check needed, _or_
      --     b) check is flagged but the base type is the one reserved for
      --        Standard.Boolean, so check does not need to be inserted.
      --        (Other boolean types in Ada have a base type of EW_Int.)

      if Eq_Base (To, From)
        and then not Do_Predicate_Check
        and then (not Do_Check
                  or else To = EW_Bool_Type)
      then
         return Expr;
      end if;

      --  Retrieve range check information

      if Do_Check then
         Get_Range_Check_Info (Ada_Node, Lvalue, Range_Type, Check_Kind);
      end if;

      return Insert_Scalar_Conversion
        (Domain      => Domain,
         Ada_Node    => Ada_Node,
         Expr        => Expr,
         To          => To,
         Range_Type  => Range_Type,
         Check_Kind  => Check_Kind,
         Lvalue      => Lvalue);
   end Insert_Scalar_Conversion;

   function Insert_Scalar_Conversion
     (Domain     : EW_Domain;
      Ada_Node   : Node_Id := Empty;
      Expr       : W_Expr_Id;
      To         : W_Type_Id;
      Range_Type : Entity_Id;
      Check_Kind : Scalar_Check_Kind;
      Lvalue     : Boolean := False) return W_Expr_Id
   is
      From : constant W_Type_Id := Get_Type (Expr);

      --  Do not generate a predicate check for an internal call to a parent
      --  predicate function inside the definition of a predicate function.
      Do_Predicate_Check : constant Boolean :=
        Present (Ada_Node)
          and then Present (Get_Ada_Node (+To))
          and then Has_Predicates (Get_Ada_Node (+To))
          and then Get_Ada_Node (+To) /= Get_Ada_Node (+From)
          and then not Is_Call_Arg_To_Predicate_Function (Ada_Node);

      --  Current result expression
      Result : W_Expr_Id := Expr;

      --  Current type of the result expression
      Cur : W_Type_Id := From;

      --  Set to True after range check has been applied
      Range_Check_Applied : Boolean := False;

   --  Start of processing for Insert_Scalar_Conversion

   begin
      --  If the check is a range check on a floating-point type, and we can
      --  determine that the expression is always within bounds, then issue
      --  a check always true. Do not apply this optimization to actual
      --  parameters of calls, as Determine_Range_R does not work for out and
      --  in out parameters, as it will return the range of the actual based
      --  on its type rather than based on the type of the formal parameter.
      --  For the same reason, do not apply also this optimization on lvalues.

      if Present (Range_Type)
        and then Is_Floating_Point_Type (Range_Type)
        and then not
          (Is_Converted_Actual_Output_Parameter (Ada_Node) or else Lvalue)
      then
         declare
            Tlo : constant Node_Id := Type_Low_Bound  (Range_Type);
            Thi : constant Node_Id := Type_High_Bound (Range_Type);
            Lov : Ureal;
            Hiv : Ureal;
            Lo  : Ureal := No_Ureal;
            Hi  : Ureal := No_Ureal;
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

               --  Call Determine_Range_R on floating-point values

               if Is_Floating_Point_Type (Etype (Ada_Node)) then
                  Determine_Range_R (Ada_Node, OK, Lo, Hi,
                                     Assume_Valid => True);

               --  Call Determine_Range on integer values, which may happen
               --  when converting an integer to a floating-point type.

               elsif Is_Discrete_Type (Etype (Ada_Node)) then
                  declare
                     use Eval_Fat;

                     function Round_Machine (B : Ureal) return Ureal is
                       (Machine (Range_Type, B, Round_Even, Ada_Node));
                     --  This is similar to the homonym function in
                     --  Checks.Determine_Range_R. It rounds a real bound B
                     --  using mode Round_Even. The underlying floating-point
                     --  type used is Range_Type.

                     Lo_Int, Hi_Int : Uint;
                  begin
                     Determine_Range (Ada_Node, OK, Lo_Int, Hi_Int,
                                      Assume_Valid => True);

                     if OK then
                        Lo := Round_Machine (UR_From_Uint (Lo_Int));
                        Hi := Round_Machine (UR_From_Uint (Hi_Int));
                     end if;
                  end;

               --  Neither a floating-point nor an integer value, hence
               --  fixed-point value. This case is not optimized for now.

               else
                  OK := False;
               end if;

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
      --  type (real for a range check of a floating point type, bitvector_?
      --  for a range check of a modular type, int for a range check of a
      --  discrete type).

      --  1. If From is an abstract type, convert it to type int, __fixed,
      --     real, or bitvector_?.

      if Get_Type_Kind (From) = EW_Abstract then
         Cur := Base_Why_Type (From);
         Result := Insert_Single_Conversion (Ada_Node => Ada_Node,
                                             Domain   => Domain,
                                             To       => Cur,
                                             Expr     => Result);
      end if;

      --  2. If From is a fixed-point type or a modular type, and To does not
      --     share the same base type (__fixed or bitvector_?), possibly
      --     convert to a suitable intermediate type.

      if Base_Why_Type (From) /= Base_Why_Type (To) then

         --  2.1. Possibly convert from one fixed-point small to another one

         if Why_Type_Is_Fixed (Base_Why_Type (From))
           and then Why_Type_Is_Fixed (Base_Why_Type (To))
         then
            declare
               From_Type : constant Entity_Id := Get_Ada_Node (+From);
               To_Type   : constant Entity_Id := Get_Ada_Node (+To);
               To_Base   : constant W_Type_Id := Base_Why_Type (To);

               --  Fixed point types always have an Ada node

               pragma Assert
                 (Present (From_Type)
                  and then Has_Fixed_Point_Type (From_Type)
                  and then Present (To_Type)
                  and then Has_Fixed_Point_Type (To_Type));

               --  If From and To have the same small, they should have the
               --  same base type.

               pragma Assert
                 (Small_Value (From_Type) /= Small_Value (To_Type));

               --  Multiply by 1 to introduce the conversion

               Module   : constant M_Fixed_Point_Mult_Div_Type :=
                 Get_Fixed_Point_Mult_Div_Theory
                   (Typ_Left   => From_Type,
                    Typ_Right  => Standard_Integer,
                    Typ_Result => To_Type);
               Name     : constant W_Identifier_Id := Module.Mult;
               One_Term : constant W_Expr_Id :=
                 New_Discrete_Constant (Value => Uint_1,
                                        Typ   => EW_Int_Type);
            begin
               Result := New_Call (Ada_Node => Ada_Node,
                                   Domain   => Domain,
                                   Name     => Name,
                                   Args     => (1 => Result,
                                                2 => One_Term),
                                   Typ      => To_Base);

               Cur := To_Base;
            end;

         --  2.2. If From is a fixed-point type and To is an integer type,

         elsif (Why_Type_Is_Fixed (Base_Why_Type (From))
                and then not Why_Type_Is_Float (Base_Why_Type (To)))

         --       or if From is a modular type and To is neither a modular nor
         --       a float, insert a convertion to int since we only support
         --       direct convertion from bitvector to int, float or another
         --       bitvector types.

           or else (Why_Type_Is_BitVector (Base_Why_Type (From))
                    and then not Why_Type_Is_BitVector (Base_Why_Type (To))
                    and then not Why_Type_Is_Float (Base_Why_Type (To)))
         then
            Result := Insert_Single_Conversion (Ada_Node => Ada_Node,
                                                Domain   => Domain,
                                                To       => EW_Int_Type,
                                                Expr     => Result);
            Cur := EW_Int_Type;
         end if;
      end if;

      --  3. Possibly perform the range check, if applicable on Cur. A special
      --     case is that range checks on boolean variables are performed after
      --     their conversion to int. Another special case is that range checks
      --     on modular types are always performed at this point, as any
      --     necessary conversion to int has already occurred in 2.

      if Present (Range_Type)
        and then not Range_Check_Applied
        and then From /= EW_Bool_Type
        and then (Base_Why_Type (Range_Type) = Cur
                   or else
                  Has_Modular_Integer_Type (Range_Type))
      then
         Range_Check_Applied := True;
         Result := +Do_Range_Check (Ada_Node   => Ada_Node,
                                    Ty         => Range_Type,
                                    W_Expr     => Result,
                                    Check_Kind => Check_Kind);
      end if;

      --  4. If From and To do not share the same base type (bool, int, __fixed
      --     bitvector_? or real), convert from one to the other.

      if Cur /= Base_Why_Type (To) then
         Result := Insert_Single_Conversion (Ada_Node => Ada_Node,
                                             Domain   => Domain,
                                             From     => Cur,
                                             To       => Base_Why_Type (To),
                                             Expr     => Result);
         Cur := Base_Why_Type (To);
      end if;

      --  5. Possibly perform the range check, if not already applied

      if Present (Range_Type)
        and then not Range_Check_Applied
      then
         pragma Assert (Base_Why_Type (Range_Type) = Cur
                        or else Base_Why_Type (Range_Type) = EW_Bool_Type
                        or else (Get_Type_Kind (Cur) = EW_Split
                          and then Base_Why_Type (Get_Ada_Node (+Cur)) =
                            Base_Why_Type (Range_Type)));
         Result := +Do_Range_Check (Ada_Node   => Ada_Node,
                                    Ty         => Range_Type,
                                    W_Expr     => Result,
                                    Check_Kind => Check_Kind);
      end if;

      --  6. Perform a predicate check if needed, before the final conversion
      --  to the target abstract type if any, if the predicate function takes
      --  a Why3 native type as input as detected by Use_Split_Form_For_Type.

      if Domain = EW_Prog
        and then Do_Predicate_Check
        and then Use_Split_Form_For_Type (Get_Ada_Node (+To))
      then
         Result := +Insert_Predicate_Check (Ada_Node => Ada_Node,
                                            Check_Ty => Get_Ada_Node (+To),
                                            W_Expr   => +Result);
      end if;

      --  7. If To is an abstract type, convert from int, __fixed or real to it

      if Get_Type_Kind (To) = EW_Abstract then
         Result := Insert_Single_Conversion (Ada_Node => Ada_Node,
                                             Domain   => Domain,
                                             From     => Cur,
                                             To       => To,
                                             Expr     => Result);

      --  If the type is in split form, no conversion is needed. Change the
      --  Ada_Node to the expected type. We do that by adding a dummy node.

      elsif Get_Type_Kind (To) = EW_Split then
         Result := New_Label (Labels => Name_Id_Sets.Empty_Set,
                              Def    => Result,
                              Domain => Domain,
                              Typ    => To);
      end if;

      --  8. Perform a predicate check if needed, after the final conversion
      --  to the target abstract type if any, if the predicate function takes
      --  an abstract type as input as detected by Use_Split_Form_For_Type.

      if Domain = EW_Prog
        and then Do_Predicate_Check
        and then not Use_Split_Form_For_Type (Get_Ada_Node (+To))
      then
         Result := +Insert_Predicate_Check (Ada_Node => Ada_Node,
                                            Check_Ty => Get_Ada_Node (+To),
                                            W_Expr   => +Result);
      end if;

      return Result;
   end Insert_Scalar_Conversion;

   ------------------------------
   -- Insert_Simple_Conversion --
   ------------------------------

   function Insert_Simple_Conversion
     (Ada_Node       : Node_Id := Empty;
      Domain         : EW_Domain;
      Expr           : W_Expr_Id;
      To             : W_Type_Id;
      Force_No_Slide : Boolean := False) return W_Expr_Id
   is
      From : constant W_Type_Id := Get_Type (Expr);

   begin

      --  Nothing to do if assigning an allocator or null or else From = To

      if not Need_Conversion (Expr)
        or else Eq_Base (To, From)
      then
         return Expr;
      end if;

      if Is_Private_Conversion (To, From)
        or else Is_Record_Conversion (To, From)
      then
         return Insert_Record_Conversion (Domain   => Domain,
                                          Ada_Node => Ada_Node,
                                          Expr     => Expr,
                                          To       => To);

      elsif Is_Array_Conversion (To, From) then
         return Insert_Array_Conversion (Domain         => Domain,
                                         Ada_Node       => Ada_Node,
                                         Expr           => Expr,
                                         To             => To,
                                         Force_No_Slide => Force_No_Slide);

      elsif Is_Pointer_Conversion (To, From) then
         return Insert_Pointer_Conversion (Domain   => Domain,
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
      From_Base : constant W_Type_Id :=
        (if Get_Type_Kind (From) = EW_Split
         and then Has_Scalar_Type (Get_Ada_Node (+From))
         then Base_Why_Type (Get_Ada_Node (+From))
         else From);
      To_Base   : constant W_Type_Id :=
        (if Get_Type_Kind (To) = EW_Split
         and then Has_Scalar_Type (Get_Ada_Node (+To))
         then Base_Why_Type (Get_Ada_Node (+To))
         else To);
   begin
      if Eq_Base (From_Base, To_Base) then
         return Expr;
      end if;

      --  Conversion of integer constants to Why range types are replaced by
      --  builtin range values.

      declare
         Current : W_Expr_Id := Expr;
      begin
         while Get_Kind (+Current) = W_Label loop
            Current := Get_Def (W_Label_Id (Current));
         end loop;

         if Get_Kind (+Current) = W_Integer_Constant
           and then Get_Type_Kind (To) = EW_Abstract
           and then Is_Range_Type_In_Why (Get_Ada_Node (+To))
         then
            return New_Range_Constant
              (Ada_Node => Get_Ada_Node (+Expr),
               Value    => Get_Value (W_Integer_Constant_Id (Current)),
               Typ      => To);
         end if;
      end;

      return
        New_Call (Domain   => Domain,
                  Ada_Node => Ada_Node,
                  Name     => Conversion_Name
                    (From => From_Base, To => To_Base),
                  Args     => (1 => +Expr),
                  Typ      => To);
   end Insert_Single_Conversion;

   -------------------------
   -- Is_Essentially_Void --
   -------------------------

   function Is_Essentially_Void (W : W_Prog_Id) return Boolean is
   begin
      return (W = +Void
              or else
                (Get_Kind (+W) = W_Label
                 and then
                 Is_Essentially_Void (+Label_Get_Def (+W)))
              or else
                (Get_Kind (+W) = W_Loc_Label
                 and then
                 Is_Essentially_Void (+Loc_Label_Get_Def (+W)))
              or else
                (Get_Kind (+W) = W_Statement_Sequence
                 and then
                 Is_Essentially_Void_List
                   (Statement_Sequence_Get_Statements (+W))));
   end Is_Essentially_Void;

   ------------------------------
   -- Is_Essentially_Void_List --
   ------------------------------

   function Is_Essentially_Void_List (L : Why_Node_List) return Boolean is
   begin
      return (for all Node of Get_List (L) => Is_Essentially_Void (+Node));
   end Is_Essentially_Void_List;

   ----------------------
   -- Is_False_Boolean --
   ----------------------

   function Is_False_Boolean (P : W_Expr_Id) return Boolean is
   begin
      return
         (Get_Kind (+P) = W_Literal and then
          Get_Value (+P) = EW_False);
   end Is_False_Boolean;

   ---------------------
   -- Is_True_Boolean --
   ---------------------

   function Is_True_Boolean (P : W_Expr_Id) return Boolean is
   begin
      return
         (Get_Kind (+P) = W_Literal and then
          Get_Value (+P) = EW_True);
   end Is_True_Boolean;

   ----------------------
   -- New_Ada_Equality --
   ----------------------

   function New_Ada_Equality
     (Typ         : Entity_Id;
      Domain      : EW_Domain;
      Left, Right : W_Expr_Id) return W_Expr_Id
   is
      Why_Type : constant W_Type_Id := Type_Of_Node (Typ);
      Use_Predef : constant Boolean :=
        not (Is_Record_Type (Get_Full_Type_Without_Checking (Typ))
             or else Is_Limited_View (Typ))
        or else No (Get_User_Defined_Eq (Base_Type (Typ)));
      Eq_Str   : constant String :=
        (if Use_Predef then "bool_eq" else "user_eq");
      Module   : constant W_Module_Id :=
        (if Is_Boolean_Type (Typ) then M_Boolean.Module else E_Module (Typ));
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
                 New_Call
                   (Name   => Why_Eq,
                    Domain => Domain,
                    Typ    => EW_Bool_Type,
                    Args   => (Left_Int, Right_Int));
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
           New_Call
             (Name   => Why_Eq,
              Domain => Domain,
              Typ    => EW_Bool_Type,
              Args   => (T, Bool_True (EW_Term)));
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
                          Name   => M_Boolean.Andb,
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
                        Name   => M_Boolean.Andb,
                        Args   => (1 => +Conjuncts (Conjuncts'First),
                                   2 => +Conjuncts (Conjuncts'First + 1)),
                        Typ    => EW_Bool_Type);
         begin
            for K in Conjuncts'First + 2 .. Conjuncts'Last loop
               Result := New_Call (Domain => Domain,
                                   Name   => M_Boolean.Andb,
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
      if Base = EW_BitVector_8_Type or else
        Base = EW_BitVector_16_Type or else
        Base = EW_BitVector_32_Type or else
        Base = EW_BitVector_64_Type
      then
         return
           New_Call (Domain => Domain,
                     Name   => MF_BVs (Base).BW_And,
                     Args   => (1 => +Left, 2 => +Right),
                     Typ    => Base);
      elsif Base = EW_Bool_Type then
         return New_And_Expr (Left, Right, Domain);
      else
         declare
            Left2  : constant W_Expr_Id :=
              (if Base = EW_Int_Type then
                  Insert_Simple_Conversion (Domain => Domain,
                                            Expr   => Left,
                                            To     => EW_Bool_Type)
               else Left);
            Right2  : constant W_Expr_Id :=
              (if Base = EW_Int_Type then
                  Insert_Simple_Conversion (Domain => Domain,
                                            Expr   => Right,
                                            To     => EW_Bool_Type)
               else Right);
         begin
            return New_And_Expr (Left2, Right2, Domain);
         end;
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
     (Ty        : Entity_Id;
      Domain    : EW_Domain;
      Attr      : Supported_Attribute_Id;
      Params    : Transformation_Params := Body_Params) return W_Expr_Id is
      Subdomain : constant EW_Domain :=
        (if Domain in EW_Prog | EW_Pterm then EW_Pterm else EW_Term);

   begin
      --  We do not generate axioms giving values to bounds of Itypes as they
      --  may contain locally defined entities that are not detected by
      --  Get_Variables ('Old, 'Loop_Entry, 'Return).

      if Attr in Attribute_First | Attribute_Last
        and then Type_Is_Modeled_As_Base (Ty)
        and then Is_Itype (Ty)
      then
         --  Use expression for dynamic bounds

         declare
            Rng : constant Node_Id := Get_Range (Ty);
            BT  : constant W_Type_Id :=
              (if Is_Standard_Boolean_Type (Ty) then EW_Int_Type
               else Base_Why_Type (Ty));
         begin
            return Transform_Expr ((if Attr = Attribute_First
                                    then Low_Bound (Rng)
                                    else High_Bound (Rng)),
                                   BT, Subdomain, Params);
         end;

      elsif Attr in Attribute_First | Attribute_Last
        and then Type_Is_Modeled_As_Base (Ty)
      then
         --  Call predefind functions

         declare
            Rng : constant Node_Id := Get_Range (Ty);
            BT  : constant W_Type_Id :=
              (if Is_Standard_Boolean_Type (Ty) then EW_Int_Type
               else Base_Why_Type (Ty));
            Bnd : constant Node_Id :=
              (if Attr = Attribute_First then Low_Bound (Rng)
               else High_Bound (Rng));
            Id  : constant W_Identifier_Id :=
              (if Attr = Attribute_First then E_Symb (Ty, WNE_Attr_First)
               else E_Symb (Ty, WNE_Attr_Last));
         begin
            return New_Call (Domain   => Subdomain,
                             Name     => Id,
                             Args     => Get_Args_From_Expression
                               (Bnd, Params.Ref_Allowed),
                             Typ      => BT);
         end;

      elsif Attr in Attribute_First | Attribute_Last | Attribute_Length
        and then Ekind (Ty) = E_String_Literal_Subtype
      then
         declare
            BT : constant W_Type_Id := Nth_Index_Rep_Type_No_Bool
              (Ty, 1);
         begin
            case Attr is
            when Attribute_First =>
               return New_Discrete_Constant
                 (Value => Expr_Value (String_Literal_Low_Bound (Ty)),
                  Typ   => BT);

            when Attribute_Length =>
               return New_Integer_Constant
                 (Value => String_Literal_Length (Ty));

            when Attribute_Last =>
               return New_Discrete_Constant
                 (Value => Expr_Value (String_Literal_Low_Bound (Ty)) +
                    String_Literal_Length (Ty) - 1,
                  Typ   => BT);

            when others =>
               raise Program_Error;
            end case;
         end;
      elsif Is_Standard_Boolean_Type (Ty) then
         case Attr is
            when Attribute_First => return +M_Boolean.First;
            when Attribute_Last  => return +M_Boolean.Last;
            when Attribute_Image => return +M_Boolean.Image;
            when Attribute_Value => return +M_Boolean.Value;
            when others =>
               raise Program_Error;
         end case;
      else
         case Attr is
            when Attribute_First       => return +E_Symb (Ty, WNE_Attr_First);
            when Attribute_Last        => return +E_Symb (Ty, WNE_Attr_Last);
            when Attribute_Alignment      =>
               return +E_Symb (Ty, WNE_Attr_Alignment);
            when Attribute_Modulus        =>
               return +E_Symb (Ty, WNE_Attr_Modulus);
            when Attribute_Constrained    =>
               return +E_Symb (Ty, WNE_Attr_Constrained);
            when Attribute_Size           =>
               return +E_Symb (Ty, WNE_Attr_Value_Size);
            when Attribute_Component_Size =>
               return +E_Symb (Ty, WNE_Attr_Component_Size);
            when Attribute_Tag            =>
               return +E_Symb (Ty, WNE_Attr_Tag);
            when Attribute_Image          =>
               return +E_Symb (Ty, WNE_Attr_Image);
            when Attribute_Value          =>
               return +E_Symb (Ty, WNE_Attr_Value);
            when others =>
               raise Program_Error;
         end case;
      end if;
   end New_Attribute_Expr;

   --------------------
   -- New_Comparison --
   --------------------

   function New_Comparison
     (Symbol      : W_Identifier_Id;
      Left, Right : W_Expr_Id;
      Domain      : EW_Domain) return W_Expr_Id
   is
      Operator : W_Identifier_Id := Symbol;
      Left1    : W_Expr_Id;
      Right1   : W_Expr_Id;
      Arg_Type : constant W_Type_Id := Get_Type (Left);
   begin

      --  The only comparisons between Boolean operands that we translate in
      --  Why without going throught integers are the equality and inequality
      --  in a predicate context, translated as equivalence or inequivalence.

      if Arg_Type = EW_Bool_Type
        and then
          ((Symbol /= Why_Eq and then Symbol /= Why_Neq)
           or else Domain /= EW_Pred)
      then
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
         Left1  := Left;
         Right1 := Right;
      end if;

      --  We enforce float equality, instead of why3 equality,
      --  when comparing floats.
      if Why_Type_Is_Float (Arg_Type) then
         if Symbol = Why_Eq then
            Operator := MF_Floats (Arg_Type).Eq;
         elsif Symbol = Why_Neq then
            Operator := MF_Floats (Arg_Type).Neq;
         end if;
      end if;

      return
        New_Call
          (Domain => Domain,
           Name   => Operator,
           Args   => (Left1, Right1),
           Typ    => EW_Bool_Type);
   end New_Comparison;

   --------------------------
   -- New_Dynamic_Property --
   --------------------------

   function New_Dynamic_Property
     (Domain : EW_Domain;
      Ty     : Entity_Id;
      Expr   : W_Expr_Id;
      Params : Transformation_Params := Body_Params) return W_Expr_Id
   is
   begin
      --  For now, only supports dynamic scalar types, unconstrained array
      --  types and record or private types with discriminants.

      if Is_Scalar_Type (Ty)
        and then (Type_Is_Modeled_As_Base (Ty)
                  or else Use_Split_Form_For_Type (Ty))
      then

         pragma Assert (not Depends_On_Discriminant (Get_Range (Ty)));

         return New_Call (Domain => Domain,
                          Name   => Dynamic_Prop_Name (Ty),
                          Args   =>
                            Args_For_Scalar_Dynamic_Property
                              (Ty, Expr, Params),
                          Typ    => EW_Bool_Type);
      elsif Is_Array_Type (Ty) and then not Is_Static_Array_Type (Ty) then
         declare
            Dim   : constant Positive := Positive (Number_Dimensions (Ty));
            Args  : W_Expr_Array (1 .. 2 * Dim);
         begin
            for Count in 0 .. Dim - 1 loop
               declare
                  F_Expr    : constant W_Expr_Id :=
                    Get_Array_Attr
                      (Domain => Domain,
                       Expr   => Expr,
                       Attr   => Attribute_First,
                       Dim    => Count + 1);
                  L_Expr : constant W_Expr_Id :=
                    Get_Array_Attr
                      (Domain => Domain,
                       Expr   => Expr,
                       Attr   => Attribute_Last,
                       Dim    => Count + 1);
               begin
                  Args (2 * Count + 1) := F_Expr;
                  Args (2 * Count + 2) := L_Expr;
               end;
            end loop;

            return New_Dynamic_Property (Domain, Ty, Args, Params);
         end;
      elsif Count_Discriminants (Ty) > 0 and then Is_Constrained (Ty) then
         declare
            Base_Expr : constant W_Expr_Id :=
              Insert_Single_Conversion (Domain   => EW_Term,
                                        Ada_Node => Ty,
                                        To       =>
                                          EW_Abstract
                                            (Root_Record_Type (Ty)),
                                        Expr     => Expr);
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

   ----------------------
   -- New_Discrete_Add --
   ----------------------

   function New_Discrete_Add
     (Domain : EW_Domain;
      Left   : W_Expr_Id;
      Right  : W_Expr_Id;
      Typ    : W_Type_Id := Why_Empty) return W_Expr_Id
   is
      Rep_Type : constant W_Type_Id :=
        (if Typ = Why_Empty
         then Base_Why_Type (Get_Type (Left))
         else Base_Why_Type (Typ));
      Op : constant W_Identifier_Id :=
        (if Rep_Type = EW_Int_Type
         then Int_Infix_Add
         else MF_BVs (Rep_Type).Add);
   begin
      pragma Assert (Rep_Type = EW_Int_Type or eLse
                     Why_Type_Is_BitVector (Rep_Type));

      return
        New_Call
          (Domain => Domain,
           Name   => Op,
           Typ    => Rep_Type,
           Args => (1 =>
                      Insert_Scalar_Conversion
                        (Domain => Domain,
                         Expr   => Left,
                         To     => Rep_Type),
                    2 =>
                      Insert_Scalar_Conversion
                        (Domain => Domain,
                         Expr   => Right,
                         To     => Rep_Type)));
   end New_Discrete_Add;

   ----------------------------
   -- New_Discrete_Substract --
   ----------------------------

   function New_Discrete_Substract
     (Domain : EW_Domain;
      Left   : W_Expr_Id;
      Right  : W_Expr_Id;
      Typ    : W_Type_Id := Why_Empty) return W_Expr_Id
   is
      Rep_Type : constant W_Type_Id :=
        (if Typ = Why_Empty
         then Base_Why_Type (Get_Type (Left))
         else Base_Why_Type (Typ));
      Op : constant W_Identifier_Id :=
        (if Rep_Type = EW_Int_Type
         then Int_Infix_Subtr
         else MF_BVs (Rep_Type).Sub);
   begin
      pragma Assert (Rep_Type = EW_Int_Type or eLse
                     Why_Type_Is_BitVector (Rep_Type));

      return
        New_Call
          (Domain => Domain,
           Name   => Op,
           Typ    => Rep_Type,
           Args => (1 =>
                      Insert_Scalar_Conversion
                        (Domain => Domain,
                         Expr   => Left,
                         To     => Rep_Type),
                    2 =>
                      Insert_Scalar_Conversion
                        (Domain => Domain,
                         Expr   => Right,
                         To     => Rep_Type)));
   end New_Discrete_Substract;

   ---------------------------
   -- New_Discrete_Constant --
   ---------------------------

   function New_Discrete_Constant
     (Ada_Node : Node_Id := Empty;
      Value    : Uint;
      Typ      : W_Type_Id) return W_Expr_Id is
     (if Why_Type_Is_BitVector (Typ)
      then New_Modular_Constant (Ada_Node, Value, Typ)
      else New_Integer_Constant (Ada_Node, Value));

   --------------------
   -- New_Havoc_Call --
   --------------------

   function New_Havoc_Call (Id : W_Identifier_Id) return W_Prog_Id is
      Havoc_Fun : constant W_Identifier_Id :=
        Havoc_Append (Get_Name (Get_Typ (Id)));
   begin
      return New_Call (Name => Havoc_Fun,
                       Args => (1 => +Id));
   end New_Havoc_Call;

   -----------------------
   -- New_Located_Label --
   -----------------------

   function New_Located_Label (Input : Source_Ptr) return Name_Id is
      Slc : Source_Ptr := Input;
      Buf : Unbounded_String;
   begin
      loop
         declare
            File   : constant String := File_Name (Slc);
            Line   : constant Physical_Line_Number :=
              Get_Physical_Line_Number (Slc);
            Column : constant Column_Number := Get_Column_Number (Slc);
         begin
            Append (Buf, File & ':' &
                         Image (Positive (Line), 1) & ':' &
                         Image (Positive (Column), 1));
            exit when Instantiation_Location (Slc) = No_Location;
            Append (Buf, (if Comes_From_Inlined_Body (Slc)
                          then ":inlined:"
                          else ":instantiated:"));
            Slc := Instantiation_Location (Slc);
         end;
      end loop;
      return NID (GP_Sloc_Marker & To_String (Buf));
   end New_Located_Label;

   -----------------------
   -- New_Located_Label --
   -----------------------

   function New_Located_Label
     (N         : Node_Id;
      Left_Most : Boolean := False)
      return Name_Id is
   begin
      return New_Located_Label (Compute_VC_Sloc (N, Left_Most));
   end New_Located_Label;

   ---------------------
   -- New_Shape_Label --
   ---------------------

   function New_Shape_Label (Node : Node_Id) return Name_Id is
      Buf : constant String := Shape_Of_Node (Node);

   begin
      if Buf /= "" then
         return NID (GP_Shape_Marker & Buf);
      else
         return No_Name;
      end if;
   end New_Shape_Label;

   -------------------------
   --  New_Comment_Label  --
   -------------------------

   function New_Comment_Label
     (Node   : Node_Id;
      Loc    : Name_Id;
      Reason : VC_Kind)
      return Name_Id
   is
      Prefix  : constant String := "comment:";
      Str_Loc : constant String := Get_Name_String (Loc);

      Pointer  : Source_Ptr := Original_Location (Sloc (Node));
      Src_Buff : constant Source_Buffer_Ptr :=
        Source_Text (Get_Source_File_Index (Pointer));

      Buf : Unbounded_String := Null_Unbounded_String;

      Line   : Natural;
      Column : Natural;

      procedure Read_Loc_Label (Line : out Natural; Column : out Natural);

      --------------------
      -- Read_Loc_Label --
      --------------------

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

   --  Start of processing for New_Comment_Label

   begin
      Read_Loc_Label (Line, Column);
      Pointer := Line_Start (Physical_Line_Number (Line),
                             Get_Source_File_Index (Pointer));

      while Src_Buff (Pointer) not in ASCII.LF | ASCII.CR
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

   -------------------------------
   -- New_Counterexample_Assign --
   -------------------------------

   function New_Counterexample_Assign (If_Node   : Node_Id;
                                       Condition : W_Expr_Id)
                                       return W_Expr_Id
   is
      Node_Label : constant Name_Id_Sets.Set :=
                        (Name_Id_Sets.To_Set
                           (NID (Branch_Id_Label &
                              Ada.Strings.Fixed.Trim
                                   (Source => Node_Id'Image (If_Node),
                                    Side   => Left))));

   begin
      return
        +Sequence
          (New_Assignment (Ada_Node => If_Node,
                           Name     =>
                             +M_Main.Spark_CE_Branch,
                           Labels   => Node_Label,
                           Value    => +Condition,
                           Typ      => EW_Bool_Type),
           New_Record_Access (Name  =>
                                +M_Main.Spark_CE_Branch,
                              Field =>
                                +New_Identifier (Name => "bool__content"),
                              Typ   => EW_Bool_Type));
   end New_Counterexample_Assign;

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
                          Name   => M_Boolean.Orb,
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
                        Name   => M_Boolean.Orb,
                        Args   => (1 => +Conjuncts (Conjuncts'First),
                                   2 => +Conjuncts (Conjuncts'First + 1)));
         begin
            for K in Conjuncts'First + 2 .. Conjuncts'Last loop
               Result := New_Call (Domain => Domain,
                                   Name   => M_Boolean.Orb,
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
      if Base = EW_BitVector_8_Type or else
        Base = EW_BitVector_16_Type or else
        Base = EW_BitVector_32_Type or else
        Base = EW_BitVector_64_Type
      then
         return
           New_Call (Domain => Domain,
                     Name   => MF_BVs (Base).BW_Or,
                     Args   => (1 => +Left, 2 => +Right),
                     Typ    => Base);
      elsif Base = EW_Bool_Type then
         return New_Or_Expr (Left, Right, Domain);
      else
         declare
            Left2  : constant W_Expr_Id :=
              (if Base = EW_Int_Type then
                  Insert_Simple_Conversion (Domain => Domain,
                                            Expr   => Left,
                                            To     => EW_Bool_Type)
               else Left);
            Right2  : constant W_Expr_Id :=
              (if Base = EW_Int_Type then
                  Insert_Simple_Conversion (Domain => Domain,
                                            Expr   => Right,
                                            To     => EW_Bool_Type)
               else Right);
         begin
            return New_Or_Expr (Left2, Right2, Domain);
         end;
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

      if Comes_From_Source (N)
        and then Is_Rewrite_Substitution (N)
        and then Nkind (Original_Node (N)) = N_And_Then
      then
         Used_Node := Right_Opnd (Original_Node (N));
      end if;

      return NID (GP_Pretty_Ada_Marker & Image (Integer (Used_Node), 1));
   end New_Sub_VC_Marker;

   --------------------
   -- New_Range_Expr --
   --------------------

   function New_Range_Expr
     (Domain    : EW_Domain;
      Low, High : W_Expr_Id;
      Expr      : W_Expr_Id) return W_Expr_Id
   is
      Ty : constant W_Type_Id :=
        (if Get_Type_Kind (Get_Type (Low)) = EW_Split
         then Base_Why_Type (Get_Ada_Node (+Get_Type (Low)))
         else Get_Type (Low));
      Le : constant W_Identifier_Id :=
        (if Ty = EW_Int_Type or else Why_Type_Is_Fixed (Ty) then Int_Infix_Le
         elsif Why_Type_Is_BitVector (Ty) then MF_BVs (Ty).Ule
         else MF_Floats (Ty).Le);
   begin
      return
         New_And_Expr
           (Left  =>
              New_Comparison
                (Domain => Domain,
                 Symbol => Le,
                 Left   => Low,
                 Right  => Expr),
            Right  =>
              New_Comparison
                (Domain => Domain,
                 Symbol => Le,
                 Left   => Expr,
                 Right  => High),
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

   -----------------------
   -- New_Function_Call --
   -----------------------

   function New_Function_Call
     (Ada_Node : Node_Id := Empty;
      Domain   : EW_Domain;
      Subp     : Node_Id;
      Selector : Selection_Kind := Why.Inter.Standard;
      Name     : W_Identifier_Id;
      Args     : W_Expr_Array;
      Typ      : W_Type_Id) return W_Expr_Id
   is
      Call : constant W_Expr_Id :=
        New_Call
           (Name     => Name,
            Args     => Args,
            Ada_Node => Ada_Node,
            Domain   => Domain,
            Typ      => Typ);
   begin
      if not Use_Guard_For_Function (Subp) then
         return Call;
      else

         --  Here we do not call directly the logic function introduced for
         --  Subp as its postcondition is not axiomatized. We rather use the
         --  post predicate associated to Subp to assume the necessary
         --  constraints on its result. We generate:
         --   (epsilon result : t. result = f args /\ post_pred result args)

         declare
            Result_Id : constant W_Identifier_Id :=
                          New_Temp_Identifier
                            (Base_Name => "result", Typ => Typ);
            Pred_Enum : constant Why_Name_Enum :=
                          (case Selector is
                              when Dispatch => WNE_Dispatch_Func_Guard,
                              when Refine   => WNE_Refined_Func_Guard,
                              when others   => WNE_Func_Guard);
         begin
            return New_Epsilon
              (Name   => Result_Id,
               Typ    => Typ,
               Domain => EW_Term,
               Pred   =>
                 +New_And_Expr
                 (New_Comparison (Symbol => Why_Eq,
                                  Domain => EW_Pred,
                                  Left   => +Result_Id,
                                  Right  => Call),
                  New_Call
                    (Name     => E_Symb (Subp, Pred_Enum),
                     Args     => +Result_Id & Args,
                     Ada_Node => Ada_Node,
                     Domain   => EW_Pred,
                     Typ      => EW_Bool_Type),
                  Domain => EW_Pred));
         end;
      end if;
   end New_Function_Call;

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
      Call : constant W_Expr_Id :=
        New_Call (Ada_Node => Ada_Node,
                  Name     => Name,
                  Args     => Progs,
                  Domain   => Domain,
                  Typ      => Typ);
   begin
      if Domain /= EW_Term then
         return +New_VC_Expr (Ada_Node => Ada_Node,
                              Reason   => Reason,
                              Expr     => Call,
                              Domain   => Domain);
      else
         return Call;
      end if;
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
      return
        Insert_Cnt_Loc_Label
          (Ada_Node => Ada_Node,
           E        =>
             New_Label
               (Ada_Node => Ada_Node,
                Labels   => New_VC_Labels (Ada_Node, Reason),
                Def      => Expr,
                Domain   => Domain,
                Typ      => Get_Type (Expr)));
   end New_VC_Expr;

   -------------------
   -- New_VC_Labels --
   -------------------

   function New_VC_Labels
     (N      : Node_Id;
      Reason : VC_Kind) return Name_Id_Set
   is
      --  A GNATprove label in Why3 has the following form
      --
      --  "GP_Reason:VC_Kind"     - the kind of the VC
      --  "GP_Sloc:file:line:col" - the sloc of the construct that triggers the
      --   VC
      --  "keep_on_simp"          - tag that disallows simplifying this VC away
      --  "model_vc"              - identifies the construct that triggers the
      --   VC and it is not postcondition (for generating counterexamples)
      --  "model_vc_post"         - identifies the construct that triggers the
      --   VC and is postcondition (for generating counterexamples)
      --
      --  For a node inside an instantiation, we use the location of the
      --  top-level instantiation. This could be refined in the future.

      Sloc : constant Source_Ptr := Compute_VC_Sloc
        (N, Left_Most => Locate_On_First_Token (Reason));
      Set : Name_Id_Set := Name_Id_Sets.Empty_Set;
      Id  : constant VC_Id := Register_VC (N, Reason, Current_Subp);
      Location_Lab : constant Name_Id := New_Located_Label (Sloc);
   begin
      if CodePeer_Has_Proved (Sloc, Reason) then
         Emit_Proof_Result
           (N,
            Id,
            Reason,
            True,
            Current_Subp,
            How_Proved => PC_Codepeer);
         Set.Insert (GP_Already_Proved);
      end if;
      Set.Insert (NID (GP_Reason_Marker & VC_Kind'Image (Reason)));
      Set.Insert (NID (GP_Id_Marker & Image (Integer (Id), 1)));
      Set.Insert (Location_Lab);

      --  Do not generate comment labels in Why3 to facilitate debugging

      if not Gnat2Why_Args.Debug_Mode then
         Set.Insert (New_Comment_Label (N, Location_Lab, Reason));
      end if;

      Set.Insert (New_Shape_Label (Node => N));
      Set.Insert (Keep_On_Simp);
      if Reason = VC_Postcondition then
         Set.Insert (Model_VC_Post);
      else
         Set.Insert (Model_VC);
      end if;
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
      if Base = EW_BitVector_8_Type or else
        Base = EW_BitVector_16_Type or else
        Base = EW_BitVector_32_Type or else
        Base = EW_BitVector_64_Type
      then
         return
           New_Call (Domain => Domain,
                     Name   => MF_BVs (Base).BW_Xor,
                     Args   => (1 => +Left, 2 => +Right),
                     Typ    => Base);

      else
         declare
            Left2  : constant W_Expr_Id :=
              (if Base = EW_Int_Type then
                  Insert_Simple_Conversion (Domain => Domain,
                                            Expr   => Left,
                                            To     => EW_Bool_Type)
               else Left);
            Right2  : constant W_Expr_Id :=
              (if Base = EW_Int_Type then
                  Insert_Simple_Conversion (Domain => Domain,
                                            Expr   => Right,
                                            To     => EW_Bool_Type)
               else Right);
            Or_Expr : constant W_Expr_Id :=
              New_Or_Expr (Left2, Right2, Domain);
            Both_Expr : constant W_Expr_Id :=
              New_And_Expr (Left2, Right2, Domain);
            Not_Both_Expr : constant W_Expr_Id :=
              (if Domain = EW_Pred then
                  New_Not (Domain => Domain, Right => Both_Expr)
               else
                  New_Call (Domain => Domain,
                            Name   => M_Boolean.Notb,
                            Args   => (1 => Both_Expr),
                            Typ    => EW_Bool_Type));
         begin
            return New_And_Expr (Or_Expr, Not_Both_Expr, Domain);
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
         return +E_Symb (Why_Ent, WNE_Dummy);
      end if;
   end Why_Default_Value;

end Why.Gen.Expr;
