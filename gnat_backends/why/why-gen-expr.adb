------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                          W H Y - G E N - E X P R                         --
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

with Ada.Strings.Unbounded; use Ada.Strings.Unbounded;

with Atree;                 use Atree;
with Einfo;                 use Einfo;
with Elists;                use Elists;
with Sem_Aux;               use Sem_Aux;
with Sinfo;                 use Sinfo;
with Sinput;                use Sinput;
with String_Utils;          use String_Utils;
with Stand;                 use Stand;

with Alfa.Util;             use Alfa.Util;

with Why.Atree.Accessors;   use Why.Atree.Accessors;
with Why.Atree.Builders;    use Why.Atree.Builders;
with Why.Atree.Tables;      use Why.Atree.Tables;
with Why.Atree.Traversal;   use Why.Atree.Traversal;
with Why.Conversions;       use Why.Conversions;
with Why.Gen.Names;         use Why.Gen.Names;
with Why.Gen.Preds;         use Why.Gen.Preds;
with Why.Inter;             use Why.Inter;

with Gnat2Why.Expr;         use Gnat2Why.Expr;
with Gnat2Why.Subprograms;  use Gnat2Why.Subprograms;
with Gnat2Why.Util;       use Gnat2Why.Util;

package body Why.Gen.Expr is

   Subp_Sloc_Map : Ada_To_Why.Map := Ada_To_Why.Empty_Map;

   --------------------------
   -- Compute_Ada_Node_Set --
   --------------------------

   function Compute_Ada_Nodeset (W : Why_Node_Id) return Node_Sets.Set is
      use Node_Sets;

      type Search_State is new Traversal_State with record
         S : Set;
      end record;

      procedure Base_Type_Pre_Op
        (State : in out Search_State;
         Node  : W_Base_Type_Id);

      procedure Identifier_Pre_Op
        (State : in out Search_State;
         Node  : W_Identifier_Id);

      procedure Integer_Constant_Pre_Op
        (State : in out Search_State;
         Node  : W_Integer_Constant_Id);
      --  Integer constants may require the use of integer infix + or -

      procedure Literal_Pre_Op
        (State : in out Search_State;
         Node  : W_Literal_Id);

      procedure Real_Constant_Pre_Op
        (State : in out Search_State;
         Node  : W_Real_Constant_Id);
      --  Real constants may require the use of real infix + or -

      procedure Analyze_Ada_Node (S : in out Set; A : Node_Id);
      --  Include if necessary node A or a node derived from A to the set S

      ----------------------
      -- Analyze_Ada_Node --
      ----------------------

      procedure Analyze_Ada_Node (S : in out Set; A : Node_Id) is
         N : Node_Id := Empty;
      begin
         if Present (A) then
            case Nkind (A) is
               when N_Identifier         |
                    N_Expanded_Name      =>
                  N := Entity (A);
               when N_String_Literal     |
                    N_Aggregate          |
                    N_Slice              |
                    N_Entity             =>
                  N := A;
               when N_Object_Declaration =>
                  N := Defining_Identifier (A);
               when others =>
                  null;
            end case;

            --  We should never depend on discriminants, unless this is the
            --  special Capacity discriminant of a formal container. In all
            --  other cases, we add a reference to the record instead.

            if Nkind (N) = N_Defining_Identifier
              and then Ekind (N) = E_Discriminant
              and then not Alfa.Util.Is_Formal_Container_Capacity (N)
            then
               N := Scope (N);
            end if;

            if Present (N) then
               S.Include (N);
            end if;
         end if;
      end Analyze_Ada_Node;

      ----------------------
      -- Base_Type_Pre_Op --
      ----------------------

      procedure Base_Type_Pre_Op
        (State : in out Search_State;
         Node  : W_Base_Type_Id)
      is
      begin
         if Get_Base_Type (+Node) = EW_Abstract then
            Analyze_Ada_Node (State.S, Get_Ada_Node (+Node));
         end if;
      end Base_Type_Pre_Op;

      -----------------------
      -- Identifier_Pre_Op --
      -----------------------

      procedure Identifier_Pre_Op
        (State : in out Search_State;
         Node  : W_Identifier_Id)
      is
      begin
         Analyze_Ada_Node (State.S, Get_Ada_Node (+Node));
      end Identifier_Pre_Op;

      -----------------------------
      -- Integer_Constant_Pre_Op --
      -----------------------------

      procedure Integer_Constant_Pre_Op
        (State : in out Search_State;
         Node  : W_Integer_Constant_Id)
      is
         N : constant Node_Id := Get_Ada_Node (+Node);
      begin
         if Present (N)
           and then Nkind (N) in N_Has_Etype
         then
            Analyze_Ada_Node (State.S, Etype (N));
         end if;
      end Integer_Constant_Pre_Op;

      --------------------
      -- Literal_Pre_Op --
      --------------------

      procedure Literal_Pre_Op
        (State : in out Search_State;
         Node  : W_Literal_Id)
      is
      begin
         Analyze_Ada_Node (State.S, Get_Ada_Node (+Node));
      end Literal_Pre_Op;

      --------------------------
      -- Real_Constant_Pre_Op --
      --------------------------

      procedure Real_Constant_Pre_Op
        (State : in out Search_State;
         Node  : W_Real_Constant_Id)
      is
         N : constant Node_Id := Get_Ada_Node (+Node);
      begin
         if Present (N)
           and then Nkind (N) in N_Has_Etype
         then
            Analyze_Ada_Node (State.S, Etype (N));
         end if;
      end Real_Constant_Pre_Op;

      SS : Search_State := (Control => Continue, S => Empty_Set);

   --  Start of Compute_Ada_Nodeset

   begin
      Traverse (SS, +W);
      return SS.S;
   end Compute_Ada_Nodeset;

   package Conversion_Reason is
      --  This package provide a rudimentary way to deleguate
      --  vc kinds to other checks. This allow to optimize out
      --  some checks without losing their reason.
      --
      --  The typical case for such a deleguation would be:
      --
      --  A : Integer := 10;
      --  B : Integer := A + 1;
      --
      --  The second line would translated as something like:
      --
      --  B := integer_from_int_ (overflow_check (integer_to_int (A) + 1))
      --
      --  Two identical checks would then be to prove: a range check by
      --  integer_from_int_, and overflow check by overflow_check. The thing
      --  is, there is little point in having two checks here, as they are
      --  strictly identical (both check that A + 1 is in range of Integer).
      --  The range check is the one to eliminate here, as it corresponds to
      --  nothing in the Ada code. But integer_from_int_ cannot be removed,
      --  So the idea is to remove overflow_check and to deleguate its
      --  reason (VC_Overflow_Check) to integer_from_int_. e.g.
      --
      --  B := #sloc# "gnatprove:VC_OVERFLOW_CHECK"
      --         integer_from_int_ (integer_to_int (A) + 1)
      --
      --  This feature can only record one reason at a time, backing up for
      --  a default if none has been pushed; we could make it a real stack;
      --  but one slot is enough for now, and what we would really need in
      --  the future is still a bit unclear, so keep it simple.

      procedure Set_Next (Reason : VC_Kind);
      --  Specify the reason for the next check that will be inserted

      function Pop return VC_Kind;
      --  Extract the reason to be included in a conversion
      --  and reset next reasons to default.

   private
      Default_Reason : constant VC_Kind := VC_Range_Check;
      Next_Reason    : VC_Kind := Default_Reason;
   end Conversion_Reason;

   -----------------------
   -- Conversion_Reason --
   -----------------------

   package body Conversion_Reason is

      ---------
      -- Pop --
      ---------

      function Pop return VC_Kind is
         Result : constant VC_Kind := Next_Reason;
      begin
         Next_Reason := Default_Reason;
         return Result;
      end Pop;

      --------------
      -- Set_Next --
      --------------

      procedure Set_Next (Reason : VC_Kind) is
      begin
         Next_Reason := Reason;
      end Set_Next;

   end Conversion_Reason;

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
            Loc  : constant Source_Ptr :=
              Translate_Location (Sloc (Uniq));
            File : constant String := File_Name (Loc);
            Line : constant Physical_Line_Number :=
              Get_Physical_Line_Number (Loc);
            Result : constant String :=
              "GP_Subp:" & File & ":" & Int_Image (Integer (Line));
            Res_Id : constant W_Identifier_Id :=
              New_Identifier (Name => Result);
         begin
            Subp_Sloc_Map.Insert (Uniq, +Res_Id);
            return Res_Id;
         end;
      end if;
   end Cur_Subp_Sloc;

   -----------------------
   -- Insert_Conversion --
   -----------------------

   function Insert_Conversion
     (Domain        : EW_Domain;
      Ada_Node      : Node_Id := Empty;
      Expr          : W_Expr_Id;
      To            : W_Base_Type_Id;
      From          : W_Base_Type_Id;
      Overflow_Type : W_Base_Type_OId := Why_Empty;
      Range_Type    : W_Base_Type_OId := Why_Empty) return W_Expr_Id
   is
      Base   : constant W_Base_Type_Id := LCA (To, From);

      function Generate_Record_Conversion
        (Ada_Node : Node_Id;
         Name     : W_Identifier_Id;
         Expr     : W_Expr_Id;
         To       : Entity_Id) return W_Expr_Id
      with Pre => Is_Record_Type (To);
      --  The entity "To" is a record type. We potentially need to add
      --  arguments to the conversion function call, this is done in
      --  this function.

      function Insert_Single_Conversion
        (To   : W_Base_Type_Id;
         From : W_Base_Type_Id;
         Expr : W_Expr_Id) return W_Expr_Id;
      --  Assuming that there is at most one step between To and From in the
      --  type hierarchy (i.e. that it exists a conversion from From
      --  to To; a counterexample would be two abstract types whose base
      --  types differ), insert the corresponding conversion.

      function Insert_Check
        (Expr : W_Expr_Id;
         By   : W_Base_Type_OId;
         Kind : VC_Kind) return W_Expr_Id;
      --  If it makes sense in the context, insert an overflow check or a range
      --  check on the top of Expr.

      --------------------------------
      -- Generate_Record_Conversion --
      --------------------------------

      function Generate_Record_Conversion
        (Ada_Node : Node_Id;
         Name     : W_Identifier_Id;
         Expr     : W_Expr_Id;
         To       : Entity_Id) return W_Expr_Id
      is
         Count       : Natural := 1;
         Constr_Elmt : Elmt_Id;

      begin
         --  When converting to a record type with discriminants that are
         --  constrained, we need to check that the constraints are satisfied.

         if Has_Discriminants (To)
           and then Present (Stored_Constraint (To))
         then
            --  Count the number of non-static constraints, which should be
            --  passed in parameter to the "of_base_" call.

            Constr_Elmt := First_Elmt (Stored_Constraint (To));
            while Present (Constr_Elmt) loop
               if not (Is_Static_Expression (Node (Constr_Elmt))) then
                  Count := Count + 1;
               end if;
               Next_Elmt (Constr_Elmt);
            end loop;

            declare
               Args      : W_Expr_Array (1 .. Count);
               Discr_Ent : Entity_Id := First_Discriminant (To);

            begin
               --  Construct the list of parameters to pass to the "of_base_"
               --  call.

               Args (1)    := Expr;
               Count       := 2;
               Constr_Elmt := First_Elmt (Stored_Constraint (To));
               while Present (Constr_Elmt) loop
                  if not (Is_Static_Expression (Node (Constr_Elmt))) then
                     Args (Count) :=
                       Transform_Expr
                         (Domain        => EW_Term,
                          Params        => Logic_Params,
                          Expr          => Node (Constr_Elmt),
                          Expected_Type => EW_Abstract (Etype (Discr_Ent)));
                     Count := Count + 1;
                  end if;
                  Next_Elmt (Constr_Elmt);
                  Next_Discriminant (Discr_Ent);
               end loop;

               pragma Assert (No (Discr_Ent));

               --  Create a call with a precondition that does the discriminant
               --  check.

               return
                 New_VC_Call
                   (Domain   => EW_Prog,
                    Ada_Node => Ada_Node,
                    Name     => To_Program_Space (Name),
                    Progs    => Args,
                    Reason   => VC_Discriminant_Check);
            end;

         --  Nothing to check otherwise

         else
            return
              New_Call
                (Domain   => Domain,
                 Ada_Node => Ada_Node,
                 Name     => Name,
                 Args     => (1 => +Expr));
         end if;
      end Generate_Record_Conversion;

      ------------------
      -- Insert_Check --
      ------------------

      function Insert_Check
        (Expr : W_Expr_Id;
         By   : W_Base_Type_OId;
         Kind : VC_Kind) return W_Expr_Id is
      begin
         if Domain /= EW_Prog
           or else Get_Base_Type (By) /= EW_Abstract
         then
            return Expr;
         end if;

         --  If To and From are equal, the conversion from the base type to
         --  To will introduce a range check that is identical to the overflow
         --  check. So do not generate the duplicated overflow check, just
         --  change the label of the next conversion.

         if Eq (To, By) then
            Conversion_Reason.Set_Next (Kind);
            return Expr;

         --  Otherwise, this is the regular case: the range check and the
         --  the overflow check will be different, so we cannot count on the
         --  conversion scheme to introduce the second.

         else
            declare
               A : constant Node_Id := Get_Ada_Node (+By);
            begin
               return
                 New_VC_Call
                   (Domain   => Domain,
                    Ada_Node => Ada_Node,
                    Name     => Prefix (Full_Name (A), WNE_Overflow, A),
                    Progs    => (1 => +Expr),
                    Reason   => Kind);
            end;
         end if;
      end Insert_Check;

      ------------------------------
      -- Insert_Single_Conversion --
      ------------------------------

      --  ??? This function is too complex. It should be rewritten when we use
      --  the frontend information for deciding where to put checks.

      function Insert_Single_Conversion
        (To   : W_Base_Type_Id;
         From : W_Base_Type_Id;
         Expr : W_Expr_Id) return W_Expr_Id is
      begin
         if Eq (From, To)

           --  ??? Special trick to ignore conversion on formal container types
           --  for the time being.

           or else
             (Present (Ada_Node)
              and then Ekind (Etype (Ada_Node)) in Record_Kind
              and then
                Alfa.Util.Type_Based_On_Formal_Container (Etype (Ada_Node)))
         then
            return Expr;
         else
            declare
               Name         : constant W_Identifier_Id :=
                 Conversion_Name (From => From, To => To);
               Check_Needed : Boolean;
               Check_Kind   : VC_Kind;
            begin

               if Domain /= EW_Prog then
                  Check_Needed := False;
               elsif Get_Base_Type (From) in EW_Scalar
                 and then not (Get_Base_Type (To) in EW_Scalar)
               then

                  --  Conversions from a base why type to an Ada type should
                  --  generate a check in program space.

                  Check_Needed := True;
                  Check_Kind   := Conversion_Reason.Pop;
               elsif
                 Get_Base_Type (From) = EW_Abstract and then
                 Get_Base_Type (To) = EW_Abstract
               then
                  Check_Needed := True;
                  Check_Kind := VC_Discriminant_Check;
               else
                  Check_Needed := False;
               end if;

               if Check_Needed then
                  if Get_Base_Type (To) = EW_Abstract
                    and then Is_Record_Type (Get_Ada_Node (+To))
                  then
                     return
                       Generate_Record_Conversion
                         (Ada_Node => Ada_Node,
                          Name     => Name,
                          Expr     => Expr,
                          To       => Get_Ada_Node (+To));
                  end if;
                  return
                    New_VC_Call
                      (Domain   => Domain,
                       Ada_Node => Ada_Node,
                       Name     => To_Program_Space (Name),
                       Progs    => (1 => +Expr),
                       Reason   => Check_Kind);

               --  In any other case (logic space, or conversions to a more
               --  general type), no check is needed.

               else
                  return
                    New_Call
                      (Domain   => Domain,
                       Ada_Node => Ada_Node,
                       Name     => Name,
                       Args     => (1 => +Expr));
               end if;
            end;
         end if;
      end Insert_Single_Conversion;

   --  Start of processing for Insert_Conversion

   begin
      if Overflow_Type /= Why_Empty then
         return
           Insert_Conversion
             (Domain   => Domain,
              Ada_Node => Ada_Node,
              To       => To,
              From     => Base,
              Expr     =>
                Insert_Check
                  (Expr =>
                     Insert_Conversion
                       (Domain   => Domain,
                        Ada_Node => Ada_Node,
                        To       => Base,
                        From     => From,
                        Expr     => Expr),
                   By   => Overflow_Type,
                   Kind => VC_Overflow_Check));

      elsif Range_Type /= Why_Empty then
         return
           Insert_Conversion
             (Domain   => Domain,
              Ada_Node => Ada_Node,
              To       => To,
              From     => Base,
              Expr     =>
                Insert_Check
                  (Expr =>
                     Insert_Conversion
                       (Domain   => Domain,
                        Ada_Node => Ada_Node,
                        To       => Base,
                        From     => From,
                        Expr     => Expr),
                   By   => Range_Type,
                   Kind => VC_Range_Check));
      end if;

      if Eq (To, From) then
         return Expr;
      end if;

      if Get_Base_Type (Base) = EW_Abstract then

         --  the case of record conversions

         return
           Insert_Single_Conversion
             (To   => To,
              From => Base,
              Expr =>
                Insert_Single_Conversion
                  (To   => Base,
                   From => From,
                   Expr => Expr));

      else

         --  the regular case

         declare
            Up_From : constant W_Base_Type_Id := Up (From, Base);
            Up_To   : constant W_Base_Type_Id := Up (To, Base);
         begin
            return
              Insert_Single_Conversion
                (To   => To,
                 From => Up_To,
                 Expr =>
                   Insert_Conversion
                     (Domain   => Domain,
                      Ada_Node => Ada_Node,
                      To       => Up_To,
                      From     => Up_From,
                      Expr     =>
                        Insert_Single_Conversion
                          (To   => Up_From,
                           From => From,
                           Expr => Expr)));
         end;
      end if;
   end Insert_Conversion;

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

      else
         if Domain = EW_Pred then
            return New_Connection
              (Domain => Domain,
               Op     => EW_And,
               Left   => +Left,
               Right  => +Right);
         else
            return
              New_Call
                (Domain => Domain,
                 Name   => To_Ident (WNE_Bool_And),
                 Args   => (1 => +Left, 2 => +Right));
         end if;
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

      else
         return New_Connection
           (Domain     => Domain,
            Op         => EW_And,
            Left       => +Conjuncts (Conjuncts'First),
            Right      => +Conjuncts (Conjuncts'First + 1),
            More_Right => Conjuncts (Conjuncts'First + 2 .. Conjuncts'Last));
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
     return W_Expr_Id
   is
      S : constant String :=
        (if Ty = Standard_Boolean then "Boolean"
         else Full_Name (Ty));
   begin
      return +Prefix (Ada_Node => Ty,
                      S        => S,
                      W        => Attr_To_Why_Name (Attr));
   end New_Attribute_Expr;

   --------------------
   -- New_Comparison --
   --------------------

   function New_Comparison
     (Cmp         : EW_Relation;
      Left, Right : W_Expr_Id;
      Arg_Types   : W_Base_Type_Id;
      Domain      : EW_Domain)
     return W_Expr_Id
   is
      Op_Type : W_Base_Type_Id;
      Left1   : W_Expr_Id;
      Right1  : W_Expr_Id;
   begin
      if Get_Base_Type (Arg_Types) = EW_Bool
        and then Cmp in EW_Inequality
      then
         Op_Type := EW_Int_Type;
         Left1  :=
           Insert_Conversion
             (Domain => Domain,
              Expr   => Left,
              From   => Arg_Types,
              To     => EW_Int_Type);
         Right1 :=
           Insert_Conversion
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
                              Domain   : EW_Domain) return W_Expr_Id
   is
   begin
      return
        New_Label (Labels => (1 => New_Located_Label (Ada_Node)),
                   Def    => Expr,
                   Domain => Domain);
   end New_Located_Expr;

   -----------------------
   -- New_Located_Label --
   -----------------------

   function New_Located_Label (N : Node_Id) return W_Identifier_Id is

      Slc : Source_Ptr := Sloc (N);
      Buf : Unbounded_String := Null_Unbounded_String;
   begin
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
      return New_Identifier (Name => "GP_Sloc:" & To_String (Buf));
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
      else
         if Domain = EW_Pred then
            return New_Connection
              (Op     => EW_Or,
               Left   => +Left,
               Right  => +Right,
               Domain => Domain);
         else
            return New_Call
              (Domain => Domain,
               Name => To_Ident (WNE_Bool_Or),
               Args => (1 => +Left, 2 => +Right));
         end if;
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
      S : constant String := String_Of_Node (N);
   begin
      if S /= "" then
         return
           New_Identifier
             (Name => To_String (WNE_Pretty_Ada) & ":" & S);
      else
         return Why_Empty;
      end if;
   end New_Pretty_Label;

   --------------------
   -- New_Range_Expr --
   --------------------

   function New_Range_Expr
     (Domain    : EW_Domain;
      Base_Type : W_Base_Type_Id;
      Low, High : W_Expr_Id;
      Expr      : W_Expr_Id) return W_Expr_Id
   is
   begin
      return
         New_And_Then_Expr
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
      --  "GP_Subp:<Subp_Sloc>"   - the sloc of the subprogram
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
         2 => Cur_Subp_Sloc,
         3 => New_Located_Label (N),
         4 => To_Ident (WNE_Keep_On_Simp));
   end New_VC_Labels;

   ------------------
   -- New_Xor_Expr --
   ------------------

   function New_Xor_Expr
      (Left, Right : W_Expr_Id;
       Domain      : EW_Domain) return W_Expr_Id is
   begin
      if Domain = EW_Pred then
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
         return
           New_Call
             (Domain => Domain,
              Name   => To_Ident (WNE_Bool_Xor),
              Args   => (1 => +Left, 2 => +Right));
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
