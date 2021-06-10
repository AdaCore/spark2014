------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                        W H Y - G E N - P R O G S                         --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                     Copyright (C) 2010-2021, AdaCore                     --
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

with Common_Containers;       use Common_Containers;
with Gnat2Why.Error_Messages; use Gnat2Why.Error_Messages;
with Gnat2Why.Subprograms;    use Gnat2Why.Subprograms;
with Gnat2Why.Util;           use Gnat2Why.Util;
with Why.Atree.Accessors;     use Why.Atree.Accessors;
with Why.Atree.Mutators;      use Why.Atree.Mutators;
with Why.Atree.Tables;        use Why.Atree.Tables;
with Why.Gen.Names;           use Why.Gen.Names;
with Why.Gen.Terms;           use Why.Gen.Terms;

package body Why.Gen.Progs is

   ------------
   -- Append --
   ------------

   procedure Append
     (Left  : in out W_Prog_Id;
      Right : W_Prog_Id)
   is
   begin
      Left := Sequence (Left, Right);
   end Append;

   procedure Append
     (Left           : in out W_Prog_Id;
      Right1, Right2 : W_Prog_Id)
   is
   begin
      Left := Sequence ((1 => Left, 2 => Right1, 3 => Right2));
   end Append;

   procedure Append
     (Left  : in out W_Expr_Id;
      Right : W_Prog_Id)
   is
   begin
      Left := +Sequence (+Left, Right);
   end Append;

   procedure Append
     (Left           : in out W_Expr_Id;
      Right1, Right2 : W_Prog_Id)
   is
   begin
      Left := +Sequence ((1 => +Left, 2 => Right1, 3 => Right2));
   end Append;

   ----------------------------------
   -- Emit_Always_True_Range_Check --
   ----------------------------------

   procedure Emit_Always_True_Range_Check
     (Ada_Node   : Node_Id;
      Check_Kind : Scalar_Check_Kind)
   is
   begin
      Emit_Static_Proof_Result (Ada_Node, To_VC_Kind (Check_Kind), True,
                                Current_Subp);
   end Emit_Always_True_Range_Check;

   -----------------------
   -- New_Any_Statement --
   -----------------------

   function New_Any_Statement
     (Ada_Node    : Node_Id;
      Pre         : W_Pred_Id;
      Post        : W_Pred_Id;
      Reason      : VC_Kind;
      Return_Type : W_Type_Id := Why_Empty)
      return W_Prog_Id is
   begin
      return
        +Insert_Cnt_Loc_Label
          (Ada_Node,
           New_Any_Expr
             (Ada_Node    => Ada_Node,
              Pre         => Pre,
              Post        => Post,
              Labels      => New_VC_Labels (Ada_Node, Reason),
              Return_Type =>
                (if Return_Type = Why_Empty then EW_Unit_Type
                 else Return_Type)));
   end New_Any_Statement;

   function New_Any_Statement
     (Ada_Node    : Node_Id := Empty;
      Post        : W_Pred_Id;
      Return_Type : W_Type_Id := Why_Empty)
      return W_Prog_Id is
   begin
      return
        New_Any_Expr
          (Ada_Node    => Ada_Node,
           Post        => Post,
           Labels      => Symbol_Sets.Empty_Set,
           Return_Type =>
             (if Return_Type = Why_Empty then EW_Unit_Type
              else Return_Type));
   end New_Any_Statement;

   --------------------------
   -- New_Assume_Statement --
   --------------------------

   function New_Assume_Statement
     (Ada_Node : Node_Id := Empty;
      Pred     : W_Pred_Id)
      return W_Prog_Id is
   begin
      if Is_True_Boolean (+Pred) then
         return +Void;
      else
         return
           New_Assert
             (Ada_Node    => Ada_Node,
              Pred        => Pred,
              Assert_Kind => EW_Assume);
      end if;
   end New_Assume_Statement;

   -------------------------
   -- New_Havoc_Statement --
   -------------------------

   function New_Havoc_Statement
     (Ada_Node : Node_Id := Empty;
      Effects  : W_Effects_Id) return W_Prog_Id is
   begin
      return
        New_Any_Expr
          (Ada_Node    => Ada_Node,
           Effects     => Effects,
           Labels      => Symbol_Sets.Empty_Set,
           Return_Type => EW_Unit_Type);
   end New_Havoc_Statement;

   ----------------
   -- New_Ignore --
   ----------------

   function New_Ignore (Ada_Node : Node_Id := Empty; Prog : W_Prog_Id)
      return W_Prog_Id
   is
      Call : constant W_Prog_Id :=
        New_Binding
          (Ada_Node => Ada_Node,
           Name     => New_Identifier
             (Domain => EW_Prog, Name => "_", Typ => Get_Type (+Prog)),
           Def      => +Prog,
           Context  => +Void,
           Typ      => EW_Unit_Type);
   begin
      return New_Abstract_Expr (Expr => Call, Post => True_Pred);
   end New_Ignore;

   --------------------------
   -- New_Located_Abstract --
   --------------------------

   function New_Located_Abstract
     (Ada_Node  : Node_Id;
      Expr      : W_Prog_Id;
      Post      : W_Pred_Id;
      Reason    : VC_Kind)
      return W_Prog_Id is
   begin
      return
        New_Abstract_Expr
          (Ada_Node => Ada_Node,
           Expr     => Expr,
           Post     =>
           +New_VC_Expr
             (Ada_Node => Ada_Node,
              Expr     => +Post,
              Reason   => Reason,
              Domain   => EW_Pred),
           Typ      => Get_Type (+Expr));
   end New_Located_Abstract;

   ------------------------
   -- New_Located_Assert --
   ------------------------

   function New_Located_Assert
      (Ada_Node : Node_Id;
       Pred     : W_Pred_Id;
       Reason   : VC_Kind;
       Kind     : EW_Assert_Kind) return W_Prog_Id
   is
      (New_Assert (Ada_Node    => Ada_Node,
                   Pred        => +New_VC_Expr (Ada_Node => Ada_Node,
                                             Expr     => +Pred,
                                             Reason   => Reason,
                                             Domain   => EW_Pred),
                   Assert_Kind => Kind));

   ------------------------
   -- New_Simpl_Any_Prog --
   ------------------------

   function New_Simpl_Any_Prog
     (T    : W_Type_Id;
      Pred : W_Pred_OId := Why_Empty) return W_Prog_Id
   is
   begin
      return
        New_Any_Expr
          (Post        => Pred,
           Labels      => Symbol_Sets.Empty_Set,
           Return_Type => +T);
   end New_Simpl_Any_Prog;

   -------------
   -- Prepend --
   -------------

   procedure Prepend
     (Left  : W_Prog_Id;
      Right : in out W_Prog_Id)
   is
   begin
      Right := Sequence (Left, Right);
   end Prepend;

   procedure Prepend
     (Left  : W_Prog_Id;
      Right : in out W_Expr_Id)
   is
   begin
      Right := +Sequence (Left, +Right);
   end Prepend;

   procedure Prepend
     (Left1, Left2  : W_Prog_Id;
      Right         : in out W_Prog_Id)
   is
   begin
      Right := Sequence ((1 => Left1, 2 => Left2, 3 => Right));
   end Prepend;

   procedure Prepend
     (Left1, Left2  : W_Prog_Id;
      Right         : in out W_Expr_Id)
   is
   begin
      Right := +Sequence ((1 => Left1, 2 => Left2, 3 => +Right));
   end Prepend;

   --------------
   -- Sequence --
   --------------

   function Sequence
     (Ada_Node    : Node_Id;
      Left, Right : W_Prog_Id)
      return W_Prog_Id
   is
   begin
      --  We only optimize the case where at least one of (Left, Right) is not
      --  a sequence; in this case we append the not-sequence statement to the
      --  sequence statement.
      --  If both are sequences, or both are non-sequences, we use
      --  New_Statement_Sequence.
      if Is_Void (Left) then
         return Right;
      elsif Is_Void (Right) then
         return Left;
      end if;

      return New_Statement_Sequence
        (Ada_Node => Ada_Node, Statements => (1 => Left, 2 => Right));
   end Sequence;

   function Sequence (Progs : W_Prog_Array) return W_Prog_Id is
      Non_Void_Progs : W_Prog_Array := Progs;
      J : Integer := Non_Void_Progs'First;
   begin
      for E of Progs loop
         if not (Is_Void (E)) then
            Non_Void_Progs (J) := E;
            J := J + 1;
         end if;
      end loop;
      if J <= Non_Void_Progs'First then
         return +Void;
      else
         return New_Statement_Sequence
           (Statements => (Non_Void_Progs (Non_Void_Progs'First .. J - 1)));
      end if;
   end Sequence;

   ---------------------
   -- Sequence_Append --
   ---------------------

   procedure Sequence_Append
     (Left  : in out W_Statement_Sequence_Id;
      Right : W_Statement_Sequence_Id)
   is
      pragma Annotate (CodePeer, Skip_Analysis);  --  for unmodified Left
      pragma Unmodified (Left);

      Stats : constant Why_Node_Lists.List :=
        Get_List (+Get_Statements (Right));
   begin
      for Stat of Stats loop
         Statement_Sequence_Append_To_Statements (Left, +Stat);
      end loop;
   end Sequence_Append;

   procedure Sequence_Append
     (Left  : in out W_Statement_Sequence_Id;
      Right : W_Prog_Id)
   is
   begin
      if Is_Void (Right) then
         null;

      elsif Get_Kind (+Right) = W_Statement_Sequence then
         Sequence_Append (Left, W_Statement_Sequence_Id'(+Right));

      else
         Statement_Sequence_Append_To_Statements (Left, Right);
      end if;
   end Sequence_Append;

   ----------------------
   -- Sequence_Prepend --
   ----------------------

   procedure Sequence_Prepend
     (Left  : W_Statement_Sequence_Id;
      Right : in out W_Statement_Sequence_Id)
   is
      pragma Annotate (CodePeer, Skip_Analysis);  --  for unmodified Right
      pragma Unmodified (Right);

      Stats : constant Why_Node_Lists.List :=
        Get_List (+Get_Statements (Left));
   begin
      for Stat of reverse Stats loop
         Statement_Sequence_Prepend_To_Statements (Right, +Stat);
      end loop;
   end Sequence_Prepend;

   procedure Sequence_Prepend
     (Left  : W_Prog_Id;
      Right : in out W_Statement_Sequence_Id)
   is
   begin
      if Is_Void (Left) then
         null;

      elsif Get_Kind (+Left) = W_Statement_Sequence then
         Sequence_Prepend (W_Statement_Sequence_Id'(+Left), Right);

      else
         Statement_Sequence_Prepend_To_Statements (Right, Left);
      end if;
   end Sequence_Prepend;

end Why.Gen.Progs;
