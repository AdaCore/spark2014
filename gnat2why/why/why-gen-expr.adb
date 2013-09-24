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
with Sem_Util;              use Sem_Util;
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
         declare
            Discr_Check_Node : constant Node_Id :=
              (if Domain = EW_Prog and Check_Needed then
                (case Nkind (Parent (Ada_Node)) is
                   when N_Assignment_Statement |
                        N_Qualified_Expression |
                        N_Type_Conversion      =>
                     Parent (Ada_Node),
                   when N_Function_Call            |
                        N_Parameter_Association    |
                        N_Procedure_Call_Statement =>
                     Ada_Node,
                   when others => Empty)
               else Empty);
         begin
            T := Insert_Record_Conversion (Domain      => Domain,
                                           Ada_Node    => Ada_Node,
                                           Expr        => T,
                                           From        => From,
                                           To          => To,
                                           Discr_Check => Discr_Check_Node);
         end;

      elsif Is_Array_Conversion (From, To) then
         declare
            Range_Check_Node : constant Node_Id :=
              (if Domain = EW_Prog and Check_Needed then
                (if Do_Range_Check (Ada_Node) then
                    Ada_Node

                 --  The flag Do_Length_Check is not set consistently in the
                 --  frontend, so check every array conversion.
                 elsif Nkind (Parent (Ada_Node)) in
                   N_Assignment_Statement     |
                   N_Qualified_Expression     |
                   N_Function_Call            |
                   N_Op_And                   |
                   N_Op_Or                    |
                   N_Op_Xor                   |
                   N_Parameter_Association    |
                   N_Procedure_Call_Statement |
                   N_Type_Conversion
                 then
                    Ada_Node
                 else Empty)
               else Empty);
         begin
            T := Insert_Array_Conversion (Domain      => Domain,
                                          Ada_Node    => Ada_Node,
                                          Expr        => T,
                                          From        => From,
                                          To          => To,
                                          Range_Check => Range_Check_Node);
         end;

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

            Round_Func : W_Identifier_Id;

         begin

            --  When converting to a floating-point or fixed-point type, from
            --  either a discrete type or another real type, rounding should
            --  be applied on the value of type real. Round_Func is the
            --  appropriate rounding function for the type.
            --
            --  When converting from a floating-point type to another
            --  floating-point type the theory takes care of the
            --  rounding and the conversion.

            if Nkind (Ada_Node) = N_Type_Conversion
              and then Ekind (Ada_Type) in Real_Kind
              and then Get_Base_Type (Base_Why_Type (To)) not in EW_Float
            then
               Round_Func := Float_Round_Name (Ada_Type);
            else
               Round_Func := Why_Empty;
            end if;

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
     (Ada_Node    : Node_Id;
      Domain      : EW_Domain;
      Expr        : W_Expr_Id;
      From        : W_Type_Id;
      To          : W_Type_Id;
      Discr_Check : Node_Id := Empty) return W_Expr_Id
   is
      --  Current result expression
      Result : W_Expr_Id := Expr;

      L : constant Node_Id := Get_Ada_Node (+From);
      R : constant Node_Id := Get_Ada_Node (+To);
      pragma Assert (Root_Record_Type (L) = Root_Record_Type (R));
      Base : constant W_Type_Id := EW_Abstract (Root_Record_Type (L));

   begin
      --  When From = To and no check needs to be inserted, do nothing

      if Eq_Base (To, From)
        and then Discr_Check = Empty
      then
         return Expr;
      end if;

      --  1. Convert From -> Base

      Result := Insert_Single_Conversion (Domain   => Domain,
                                          Ada_Node => Ada_Node,
                                          To       => Base,
                                          From     => From,
                                          Expr     => Result);

      --  2. Possibly perform the discriminant check

      if Present (Discr_Check) then
         declare
            Check_Entity : constant Entity_Id :=
              (case Nkind (Discr_Check) is
                  when N_Assignment_Statement =>
                     Unique_Entity (Etype (Name (Discr_Check))),
                  when N_Qualified_Expression |
                       N_Type_Conversion      =>
                     Unique_Entity (Etype (Discr_Check)),
                  when others =>  --  Reach here only for actual parameters
                     Get_Formal_Type_From_Actual (Discr_Check));
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
         case Get_Base_Type (Op_Type) is
            when EW_Float =>
               return New_Call
                 (Domain => Domain,
                  Name   => To_Fp_Ident (Get_Base_Type (Op_Type), Cmp),
                  Args   => (1 => +Left1,
                             2 => +Right1));

            when others =>
               return New_Relation
                 (Domain  => Domain,
                  Op_Type => Get_Base_Type (Op_Type),
                  Left    => +Left1,
                  Right   => +Right1,
                  Op      => Cmp);
         end case;
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

      declare
         P : Source_Ptr := Slc;
         Print_Src : Boolean := False;
      begin
         loop
            declare
               File : constant String := File_Name (P);
               Line   : constant Physical_Line_Number :=
                 Get_Physical_Line_Number (P);
               Column : constant Column_Number := Get_Column_Number (P);
            begin
               Append (Buf, File);
               if Print_Src then
                  Append (Buf, "_");
                  Append (Buf, Int_Image (Integer (Line)));
                  Append (Buf, '_');
                  Append (Buf, Int_Image (Integer (Column)));
               end if;
               P := Instantiation_Location (P);
               exit when P = No_Location;
               Append (Buf, "__");
               Print_Src := True;
            end;
         end loop;
      end;

      declare
         Line   : constant Physical_Line_Number :=
           Get_Physical_Line_Number (Slc);
         Column : constant Column_Number := Get_Column_Number (Slc);
      begin
         Append (Buf, ':');
         Append (Buf, Int_Image (Integer (Line)));
         Append (Buf, ':');
         Append (Buf, Int_Image (Integer (Column)));
      end;

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
