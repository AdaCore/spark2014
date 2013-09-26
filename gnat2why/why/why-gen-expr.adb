------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                          W H Y - G E N - E X P R                         --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                       Copyright (C) 2010-2013, AdaCore                   --
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

with Ada.Strings.Unbounded; use Ada.Strings.Unbounded;

with Atree;                 use Atree;
with Einfo;                 use Einfo;
with Errout;                use Errout;
with Sem_Eval;              use Sem_Eval;
with Sinfo;                 use Sinfo;
with Sinput;                use Sinput;
with String_Utils;          use String_Utils;
with Stand;                 use Stand;
with Uintp;                 use Uintp;

with SPARK_Util;            use SPARK_Util;

with Why.Atree.Accessors;   use Why.Atree.Accessors;
with Why.Atree.Builders;    use Why.Atree.Builders;
with Why.Atree.Tables;      use Why.Atree.Tables;
with Why.Conversions;       use Why.Conversions;
with Why.Gen.Arrays;        use Why.Gen.Arrays;
with Why.Gen.Names;         use Why.Gen.Names;
with Why.Gen.Preds;         use Why.Gen.Preds;
with Why.Gen.Progs;         use Why.Gen.Progs;
with Why.Gen.Records;       use Why.Gen.Records;
with Why.Inter;             use Why.Inter;

with Gnat2Why.Expr;         use Gnat2Why.Expr;
with Gnat2Why.Nodes;        use Gnat2Why.Nodes;
with Gnat2Why.Subprograms;  use Gnat2Why.Subprograms;

package body Why.Gen.Expr is

   function Insert_Single_Conversion
     (Ada_Node : Node_Id;
      Domain   : EW_Domain;
      To       : W_Type_Id;
      From     : W_Type_Id;
      Expr     : W_Expr_Id) return W_Expr_Id;
   --  Assuming that there is at most one step between To and From in the
   --  type hierarchy (i.e. that it exists a conversion from From
   --  to To; a counterexample would be two abstract types whose base
   --  types differ), insert the corresponding conversion.

   Subp_Sloc_Map : Ada_To_Why.Map := Ada_To_Why.Empty_Map;

   -------------------
   -- Cur_Subp_Sloc --
   -------------------

   function Cur_Subp_Sloc return W_Identifier_Id is
      Uniq : constant Entity_Id := Current_Subp;
      Cur : constant Ada_To_Why.Cursor :=
        Subp_Sloc_Map.Find (Uniq);
   begin
      if Ada_To_Why.Has_Element (Cur) then
         return +Ada_To_Why.Element (Cur);
      else
         declare
            Res_Id : constant W_Identifier_Id :=
              New_Identifier (Name => Subp_Location (Uniq));
         begin
            Subp_Sloc_Map.Insert (Uniq, +Res_Id);
            return Res_Id;
         end;
      end if;
   end Cur_Subp_Sloc;

   -------------------------
   -- Cur_Subp_Name_Label --
   -------------------------

   function Cur_Subp_Name_Label
      return W_Identifier_Id is
   begin
      return
        New_Identifier
          (Name => To_String (WNE_Pretty_Ada) & ":" &
               Subprogram_Full_Source_Name (Current_Subp));
   end Cur_Subp_Name_Label;

   -----------------------------
   -- Insert_Array_Conversion --
   -----------------------------

   function Insert_Array_Conversion
     (Domain     : EW_Domain;
      Ada_Node   : Node_Id := Empty;
      Expr       : W_Expr_Id;
      To         : W_Type_Id;
      From       : W_Type_Id;
      Need_Check : Boolean := False) return W_Expr_Id
   is
      To_Ent    : constant Entity_Id := Get_Ada_Node (+To);
      From_Ent  : constant Entity_Id := Get_Ada_Node (+From);
      Dim       : constant Positive := Positive (Number_Dimensions (To_Ent));

      function Needs_Slide (From_Ent, To_Ent : Entity_Id) return Boolean;
      --  Check whether a conversion between those types requires sliding.

      function Insert_Length_Check
        (Expr             : W_Expr_Id;
         From_Ent, To_Ent : Entity_Id) return W_Prog_Id;

      function Insert_Array_Range_Check
        (Expr             : W_Expr_Id;
         From_Ent, To_Ent : Entity_Id) return W_Prog_Id;

      ------------------------------
      -- Insert_Array_Range_Check --
      ------------------------------

      function Insert_Array_Range_Check
        (Expr             : W_Expr_Id;
         From_Ent, To_Ent : Entity_Id) return W_Prog_Id
      is
         Check   : W_Pred_Id;
         Args    : W_Expr_Array (1 .. 2 * Dim);
         Arg_Ind : Positive := 1;
      begin
         for I in 1 .. Dim loop
            Add_Attr_Arg
              (EW_Prog, Args, Expr, From_Ent, Attribute_First, I, Arg_Ind);
            Add_Attr_Arg
              (EW_Prog, Args, Expr, From_Ent, Attribute_Last, I, Arg_Ind);
         end loop;
         Check :=
           New_Call (Name   =>
                       Prefix (Ada_Node => To_Ent,
                               P        => Full_Name (To_Ent),
                               N        => "range_check"),
                     Args   => Args);
         return New_Located_Assert (Ada_Node, Check, VC_Range_Check);
      end Insert_Array_Range_Check;

      -------------------------
      -- Insert_Length_Check --
      -------------------------

      function Insert_Length_Check
        (Expr             : W_Expr_Id;
         From_Ent, To_Ent : Entity_Id) return W_Prog_Id
      is
         Check : W_Pred_Id := True_Pred;
      begin
         for I in 1 .. Dim loop
            declare
               Input_Length    : constant W_Expr_Id :=
                 Build_Length_Expr (Domain, Expr, From_Ent, I);
               Expected_Length : constant W_Expr_Id :=
                 Build_Length_Expr (Domain, Why_Empty, To_Ent, I);
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
         return New_Located_Assert (Ada_Node, Check, VC_Length_Check);
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
                 Expr_Value (Low_From) /= Expr_Value (Low_To) then
                  return True;
               end if;
            end;
         end loop;

         --  We statically know that the "first" are actually equal, no sliding
         --  needed

         return False;
      end Needs_Slide;

      Needs_Tmp   : Boolean := False;
      Sliding     : constant Boolean := Needs_Slide (From_Ent, To_Ent);
      Tmp_Var     : W_Identifier_Id;
      Arr_Expr    : W_Expr_Id;
      T           : W_Expr_Id;
      Arg_Ind     : Positive := 1;

      --  Beginning of processing for Insert_Array_Conversion

   begin

      if To_Ent = From_Ent then

         --  No range check needed

         return Expr;
      end if;

      --  We need a temp whenever there is a sliding, or when the "from" is
      --  unconstrained, and only when the expression is not a variable already

      Needs_Tmp := Get_Kind (+Expr) not in W_Identifier | W_Deref
                     and then (Sliding or else not Is_Constrained (From_Ent));

      if Needs_Tmp then
         Tmp_Var := New_Temp_Identifier;
         Arr_Expr := +Tmp_Var;
      else
         Arr_Expr := Expr;
      end if;

      --  ??? do not forget range checks

      if Is_Constrained (To_Ent) then
         if Sliding then
            declare
               Args    : W_Expr_Array (1 .. 1 + 2 * Dim);
            begin
               Add_Map_Arg (Domain, Args, Arr_Expr, From_Ent, Arg_Ind);
               for I in 1 .. Dim loop
                  Add_Attr_Arg
                    (Domain, Args, Arr_Expr, From_Ent,
                     Attribute_First, Dim, Arg_Ind);
                  Add_Attr_Arg
                    (Domain, Args, Arr_Expr, To_Ent,
                     Attribute_First, Dim, Arg_Ind);
               end loop;
               T := New_Call
                 (Domain => Domain,
                  Name   =>
                    Prefix (P => To_String (Ada_Array_Name (Int (Dim))),
                            N => "slide"),
                  Args   => Args);
            end;
         elsif not Is_Constrained (From_Ent) then
               T :=
                 New_Call
                   (Domain => Domain,
                    Name   =>
                      Prefix (Ada_Node => From_Ent,
                              S        => Full_Name (From_Ent),
                              W        => WNE_To_Array),
                    Args => (1 => Arr_Expr));
         else
            T := Arr_Expr;
         end if;
      else
         declare
            Args     : W_Expr_Array (1 .. 2 * Dim + 1);
            Arg_Ind  : Positive := 1;
         begin
            Add_Array_Arg (Domain, Args, Arr_Expr, From_Ent, Arg_Ind);
            T :=
              New_Call
                (Domain => Domain,
                 Name   =>
                   Prefix (Ada_Node => To_Ent,
                           S        => Full_Name (To_Ent),
                           W        => WNE_Of_Array),
                 Args => Args);
         end;
      end if;

      if Domain = EW_Prog and Need_Check then
         declare
            Check_Type : constant Entity_Id := Get_Ada_Node (+To);
         begin
            if Is_Constrained (Check_Type) then
               T := +Sequence
                 (Insert_Length_Check (Arr_Expr, From_Ent, Check_Type),
                  +T);
            else
               T := +Sequence
                 (Insert_Array_Range_Check (Arr_Expr, From_Ent, Check_Type),
                 +T);
            end if;
         end;
      end if;

      if Needs_Tmp then
         T :=
           New_Binding
             (Domain  => Domain,
              Name    => Tmp_Var,
              Def     => +Expr,
              Context => T);
      end if;
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
      To       : W_Type_Id;
      From     : W_Type_Id) return W_Expr_Id
   is
      --  When converting between Ada types, detect cases where a check is not
      --  needed.

      Check_Needed : constant Boolean :=
        (if Get_Base_Type (From) = EW_Abstract
              and
            Get_Base_Type (To) = EW_Abstract
         then
            Check_Needed_On_Conversion (From => Get_Ada_Node (+From),
                                        To   => Get_Ada_Node (+To))
         else
            True);

      T : W_Expr_Id := Expr;

   begin
      --  Conversion between record types need to go through their common root
      --  record type. A discriminant check may be needed. Currently perform it
      --  on all discriminant record types, as the flag Do_Discriminant_Check
      --  is not set appropriately by the frontend on type conversions.

      if Is_Record_Conversion (From, To) then
         T := Insert_Record_Conversion (Domain     => Domain,
                                        Ada_Node   => Ada_Node,
                                        Expr       => T,
                                        From       => From,
                                        To         => To,
                                        Need_Check => Check_Needed);

      elsif Is_Array_Conversion (From, To) then
         --  The flag Do_Length_Check is not set consistently in the
         --  frontend, so check every array conversion.

         T := Insert_Array_Conversion (Domain     => Domain,
                                       Ada_Node   => Ada_Node,
                                       Expr       => T,
                                       From       => From,
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

            Range_Check_Node : constant Node_Id :=
              (if Domain = EW_Prog and Check_Needed then
                 (if Do_Range_Check (Ada_Node) then
                    Ada_Node
                  elsif Nkind (Parent (Ada_Node)) = N_Type_Conversion
                    and then Do_Overflow_Check (Parent (Ada_Node))
                  then
                    Ada_Node
                  else Empty)
               else Empty);

            --  When converting to a floating-point or fixed-point type, from
            --  either a discrete type or another real type, rounding should
            --  be applied on the value of type real. Round_Func is the
            --  appropriate rounding function for the type.

            Round_Func : constant W_Identifier_Id :=
              (if Nkind (Ada_Node) = N_Type_Conversion
                 and then Ekind (Ada_Type) in Real_Kind
               then
                  Float_Round_Name (Ada_Type)
               else Why_Empty);

         begin
            T := Insert_Scalar_Conversion (Domain      => Domain,
                                           Ada_Node    => Ada_Node,
                                           Expr        => T,
                                           From        => From,
                                           To          => To,
                                           Round_Func  => Round_Func,
                                           Range_Check => Range_Check_Node);
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
      From       : W_Type_Id;
      To         : W_Type_Id;
      Need_Check : Boolean := False) return W_Expr_Id
   is
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
                                          From     => From,
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
                                          From     => Base,
                                          Expr     => Result);

      return Result;
   end Insert_Record_Conversion;

   ------------------------------
   -- Insert_Scalar_Conversion --
   ------------------------------

   function Insert_Scalar_Conversion
     (Domain        : EW_Domain;
      Ada_Node      : Node_Id := Empty;
      Expr          : W_Expr_Id;
      To            : W_Type_Id;
      From          : W_Type_Id;
      Round_Func    : W_Identifier_Id := Why_Empty;
      Range_Check   : Node_Id := Empty) return W_Expr_Id
   is
      --  Current result expression
      Result : W_Expr_Id := Expr;

      --  Current type of the result expression
      Cur : W_Type_Id := From;

      --  Type and kind for the range check
      Range_Type : Entity_Id;
      Check_Kind : Range_Check_Kind;

      --  Set to True after range check has been applied
      Range_Check_Applied : Boolean := False;

   begin
      --  When From = To and no check nor rounding needs to be inserted, do
      --  nothing.

      if Eq_Base (To, From)
        and then No (Range_Check)
        and then No (Round_Func)
      then
         return Expr;
      end if;

      --  Retrieve range check information

      if Present (Range_Check) then
         Get_Range_Check_Info (Range_Check, Range_Type, Check_Kind);
      end if;

      --  the regular case, we take care to insert the range check at a
      --  valid place where the expression is of the appropriate Why base
      --  type (real for a range check of a floating point type, int for a
      --  range check of a discrete type).

      --  1. If From is an abstract type, convert it to type int or real

      if Get_Base_Type (From) = EW_Abstract then
         Cur := Base_Why_Type (From);
         Result := Insert_Single_Conversion (Ada_Node => Ada_Node,
                                             Domain   => Domain,
                                             To       => Cur,
                                             From     => From,
                                             Expr     => Result);
      end if;

      --  2. Possibly perform the range check, if applicable on Cur. A special
      --     case is that range checks on boolean variables are performed after
      --     their conversion to int.

      if Present (Range_Check)
        and then Base_Why_Type (Range_Type) = Cur
        and then Get_Base_Type (From) /= EW_Bool
      then
         Range_Check_Applied := True;
         Result := Insert_Range_Check (Range_Check, Result);
      end if;

      --  3. If From and To do not share the same base type (bool, int or
      --     real), convert from one to the other.

      if Base_Why_Type (From) /= Base_Why_Type (To) then
         declare
            Save : constant W_Type_Id := Cur;
         begin
            Cur := Base_Why_Type (To);
            Result := Insert_Single_Conversion (Ada_Node => Ada_Node,
                                                Domain   => Domain,
                                                To       => Cur,
                                                From     => Save,
                                                Expr     => Result);
         end;
      end if;

      --  4. When converting to a floating-point or fixed-point type, always
      --     perform a rounding operation.

      if Present (Round_Func) then
         pragma Assert (Get_Base_Type (Cur) = EW_Real);
         Result := New_Call (Domain   => Domain,
                             Name     => Round_Func,
                             Args     => (1 => Result));
      end if;

      --  5. Possibly perform the range check, if not already applied

      if Present (Range_Check)
        and then not Range_Check_Applied
      then
         pragma Assert (Base_Why_Type (Range_Type) = Cur
                          or else
                        Base_Why_Type (Range_Type) = EW_Bool_Type);
         Result := Insert_Range_Check (Range_Check, Result);
      end if;

      --  6. If To is an abstract type, convert from int or real to it

      if Get_Base_Type (To) = EW_Abstract then
         Result := Insert_Single_Conversion (Ada_Node => Ada_Node,
                                             Domain   => Domain,
                                             To       => To,
                                             From     => Cur,
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
      To       : W_Type_Id;
      From     : W_Type_Id) return W_Expr_Id is
   begin
      --  Nothing to do if From = To

      if Eq_Base (To, From) then
         return Expr;
      end if;

      if Is_Record_Conversion (To, From) then
         return Insert_Record_Conversion (Domain   => Domain,
                                          Ada_Node => Ada_Node,
                                          Expr     => Expr,
                                          From     => From,
                                          To       => To);

      elsif Is_Array_Conversion (To, From) then
         return Insert_Array_Conversion (Domain   => Domain,
                                         Ada_Node => Ada_Node,
                                         Expr     => Expr,
                                         From     => From,
                                         To       => To);

      else
         return Insert_Scalar_Conversion (Domain   => Domain,
                                          Ada_Node => Ada_Node,
                                          Expr     => Expr,
                                          From     => From,
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
      From     : W_Type_Id;
      Expr     : W_Expr_Id) return W_Expr_Id
   is
   begin
      if Eq_Base (From, To) then
         return Expr;
      end if;

      return New_Call (Domain   => Domain,
                       Ada_Node => Ada_Node,
                       Name     => Conversion_Name (From => From, To => To),
                       Args     => (1 => +Expr));
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
                          Args   => (1 => +Left, 2 => +Right));
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
                                   2 => +Conjuncts (Conjuncts'First + 1)));
         begin
            for K in Conjuncts'First + 2 .. Conjuncts'Last loop
               Result := New_Call (Domain => Domain,
                                   Name   => To_Ident (WNE_Bool_And),
                                   Args   => (1 => Result,
                                              2 => +Conjuncts (K)));
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
                     Name   => To_Ident (WNE_Bitwise_And),
                     Args   => (1 => +Left, 2 => +Right));
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

   function New_Attribute_Expr (Ty : Entity_Id; Attr : Attribute_Id)
     return W_Expr_Id is
   begin
      if Attr in Attribute_First | Attribute_Last | Attribute_Length and then
        Ekind (Ty) = E_String_Literal_Subtype then
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
            S : constant String :=
              (if Ty = Standard_Boolean then "Boolean"
               else Full_Name (Ty));
         begin
            return +Prefix (Ada_Node => Ty,
                            S        => S,
                            W        => Attr_To_Why_Name (Attr));
         end;
      end if;
   end New_Attribute_Expr;

   --------------------
   -- New_Comparison --
   --------------------

   function New_Comparison
     (Cmp         : EW_Relation;
      Left, Right : W_Expr_Id;
      Arg_Types   : W_Type_Id;
      Domain      : EW_Domain)
     return W_Expr_Id
   is
      Op_Type : W_Type_Id;
      Left1   : W_Expr_Id;
      Right1  : W_Expr_Id;

   begin
      --  The only comparisons between Boolean operands that we translate in
      --  Why without going throught integers are the equality and inequality
      --  in a predicate context, translated as equivalence or inequivalence.

      if Get_Base_Type (Arg_Types) = EW_Bool
        and then (Cmp in EW_Inequality or else Domain /= EW_Pred)
      then
         Op_Type := EW_Int_Type;
         Left1  :=
           Insert_Simple_Conversion
             (Domain => Domain,
              Expr   => Left,
              From   => Arg_Types,
              To     => EW_Int_Type);
         Right1 :=
           Insert_Simple_Conversion
             (Domain => Domain,
              Expr   => Right,
              From   => Arg_Types,
              To     => EW_Int_Type);
      else
         Op_Type := Arg_Types;
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
              Domain => Domain);
      end if;
   end New_Comparison;

   ----------------------
   -- New_Located_Expr --
   ----------------------

   function New_Located_Expr (Ada_Node : Node_Id;
                              Expr     : W_Expr_Id;
                              Domain   : EW_Domain;
                              Is_VC    : Boolean) return W_Expr_Id
   is
   begin
      return
        New_Label (Labels => (1 => New_Located_Label (Ada_Node, Is_VC)),
                   Def    => Expr,
                   Domain => Domain);
   end New_Located_Expr;

   -----------------------
   -- New_Located_Label --
   -----------------------

   function New_Located_Label
     (N         : Node_Id;
      Is_VC     : Boolean;
      Left_Most : Boolean := False)
      return W_Identifier_Id
   is
      Slc    : Source_Ptr;
      Buf    : Unbounded_String := Null_Unbounded_String;
      Prefix : constant String :=
        (if Is_VC then "GP_Sloc_VC:" else "GP_Sloc:");
   begin

      --  For VCs, we mostly want to point directly to the relevant node [N].
      --  For other nodes (e.g. pretty printing labels) it's more sensible to
      --  point to the beginning of the expression instead of the operator.
      --  This is achieved by calling [First_Sloc] instead of [Sloc]. However,
      --  [First_Sloc] does not work for N_And_Then nodes in assertions which
      --  are rewritten in a strange manner, so we do not do this optimization
      --  in that case. See also [New_Pretty_Label].

      if (not Left_Most and then Is_VC) or else
        (Comes_From_Source (N) and then Original_Node (N) /= N and then
        Nkind (Original_Node (N)) = N_And_Then) then
         Slc := Sloc (N);
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
            Slc := Instantiation_Location (Slc);
            exit when Slc = No_Location;
            Append (Buf, ':');
         end;
      end loop;
      return New_Identifier (Name => Prefix & To_String (Buf));
   end New_Located_Label;

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
                          Args   => (1 => +Left, 2 => +Right));
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
                                              2 => +Conjuncts (K)));
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
                     Name   => To_Ident (WNE_Bitwise_Or),
                     Args   => (1 => +Left, 2 => +Right));
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

   ----------------------
   -- New_Pretty_Label --
   ----------------------

   function New_Pretty_Label (N : Node_Id) return W_Identifier_Id
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
        Nkind (Original_Node (N)) = N_And_Then then
         Used_Node := Right_Opnd (Original_Node (N));
      end if;
      declare
         S : constant String := String_Of_Node (Used_Node);
      begin
         if S /= "" then
            return
              New_Identifier
                (Name => To_String (WNE_Pretty_Ada) & ":" & S);
         else
            return Why_Empty;
         end if;
      end;
   end New_Pretty_Label;

   --------------------
   -- New_Range_Expr --
   --------------------

   function New_Range_Expr
     (Domain    : EW_Domain;
      Base_Type : W_Type_Id;
      Low, High : W_Expr_Id;
      Expr      : W_Expr_Id) return W_Expr_Id
   is
   begin
      return
         New_And_Expr
           (Left  =>
              New_Comparison
                (Domain    => Domain,
                 Arg_Types => Base_Type,
                 Cmp       => EW_Le,
                 Left      => +Low,
                 Right     => +Expr),
            Right  =>
              New_Comparison
                (Domain    => Domain,
                 Arg_Types => Base_Type,
                 Cmp       => EW_Le,
                 Left      => +Expr,
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
              Domain    => Domain);
      end if;
   end New_Simpl_Conditional;

   -----------------
   -- New_VC_Call --
   -----------------

   function New_VC_Call
      (Ada_Node : Node_Id;
       Name     : W_Identifier_Id;
       Progs    : W_Expr_Array;
       Reason   : VC_Kind;
       Domain   : EW_Domain) return W_Expr_Id
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
                Domain   => Domain),
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
               Domain   => Domain);
      else
         return Expr;
      end if;
   end New_VC_Expr;

   -------------------
   -- New_VC_Labels --
   -------------------

   function New_VC_Labels (N : Node_Id; Reason : VC_Kind)
      return W_Identifier_Array
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

   begin
      return
        (1 => New_Identifier
           (Name => "GP_Reason:" & VC_Kind'Image (Reason)),
         2 =>
           New_Located_Label
             (N,
              Is_VC => True,
              Left_Most => Is_Assertion_Kind (Reason)),
         3 => To_Ident (WNE_Keep_On_Simp));
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
              To_Ident
                (if Base = EW_Bool_Type then WNE_Bool_Xor
                 else WNE_Bitwise_Xor);
         begin
            return
              New_Call
                (Domain => Domain,
                 Name   => Id,
                 Args   => (1 => +Left, 2 => +Right));
         end;
      end if;
   end New_Xor_Expr;

   -----------------------
   -- Why_Default_Value --
   -----------------------

   function Why_Default_Value (Domain : EW_Domain;
                               E      : Entity_Id) return W_Expr_Id
   is
   begin
      if E = Standard_Boolean then
         return New_Literal (Domain => Domain, Value => EW_True);
      else
         return +New_Identifier (Ada_Node => E,
                                 Domain  => Domain,
                                 Context => Full_Name (E),
                                 Name    => To_String (WNE_Dummy));
      end if;
   end Why_Default_Value;

end Why.Gen.Expr;
