------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                        W H Y - G E N - P R O G S                         --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                       Copyright (C) 2010-2017, AdaCore                   --
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

with Gnat2Why.Error_Messages; use Gnat2Why.Error_Messages;
with Gnat2Why.Subprograms;    use Gnat2Why.Subprograms;
with Why.Atree.Modules;       use Why.Atree.Modules;
with Why.Conversions;         use Why.Conversions;
with Why.Gen.Expr;            use Why.Gen.Expr;
with Why.Gen.Names;           use Why.Gen.Names;

package body Why.Gen.Progs is

   ------------------------------------
   -- Insert_Always_True_Range_Check --
   ------------------------------------

   procedure Emit_Always_True_Range_Check
     (Ada_Node   : Node_Id;
      Check_Kind : Range_Check_Kind)
   is
      Id : constant VC_Id := Register_VC (Ada_Node, Current_Subp);
   begin
      Emit_Proof_Result
        (Ada_Node,
         Id,
         To_VC_Kind (Check_Kind),
         True,
         Current_Subp,
         How_Proved => PC_Interval);
   end Emit_Always_True_Range_Check;

   -----------------------
   -- New_Any_Statement --
   -----------------------

   function New_Any_Statement
     (Ada_Node    : Node_Id := Empty;
      Pre         : W_Pred_Id := True_Pred;
      Post        : W_Pred_Id;
      Return_Type : W_Type_Id := Why_Empty)
      return W_Prog_Id is
   begin
      return
        New_Any_Expr
          (Ada_Node => Ada_Node,
           Pre      => Pre,
           Post     => Post,
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
      return
        New_Assert
          (Ada_Node    => Ada_Node,
           Pred        => Pred,
           Assert_Kind => EW_Assume);
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
          (Ada_Node => Ada_Node,
           Effects  => Effects,
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
           Name     => New_Identifier (Domain => EW_Prog, Name => "_"),
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

   function New_Located_Assert
      (Ada_Node : Node_Id;
       Pred     : W_Pred_Id;
       Kind     : EW_Assert_Kind) return W_Prog_Id
   is
      (New_Located_Assert (Ada_Node, Pred, VC_Assert, Kind));

   ----------------
   -- New_Result --
   ----------------

   function New_Result
     (T : W_Type_Id)
     return W_Binder_Id is
   begin
      return New_Binder
        (Domain   => EW_Term,
         Name     => New_Result_Ident (T),
         Arg_Type => T);
   end New_Result;

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
           Return_Type => +T);
   end New_Simpl_Any_Prog;

   --------------
   -- Sequence --
   --------------

   function Sequence (Left, Right : W_Prog_Id) return W_Prog_Id is

   --  Start of processing for Sequence

   begin
      --  We only optimize the case where at least one of (Left, Right) is not
      --  a sequence; in this case we append the not-sequence statement to the
      --  sequence statement.
      --  If both are sequences, or both are non-sequences, we use
      --  New_Statement_Sequence.
      if Left = +Void then
         return Right;
      elsif Right = +Void then
         return Left;
      end if;

      return New_Statement_Sequence
        (Statements => (1 => Left, 2 => Right));
   end Sequence;

   function Sequence (Progs : W_Prog_Array) return W_Prog_Id is
      Result : W_Prog_Id := Progs (Progs'First);
   begin
      for J in Progs'First + 1 .. Progs'Last loop
         Result := Sequence (Result, Progs (J));
      end loop;
      return Result;
   end Sequence;

end Why.Gen.Progs;
