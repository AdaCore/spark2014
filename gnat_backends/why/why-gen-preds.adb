------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                        W H Y - G E N - P R E D S                         --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                       Copyright (C) 2010-2011, AdaCore                   --
--                                                                          --
-- gnat2why is  free  software;  you can redistribute it and/or modify it   --
-- under terms of the  GNU General Public License as published  by the Free --
-- Software Foundation;  either version  2,  or  (at your option) any later --
-- version. gnat2why is distributed in the hope that it will  be  useful,   --
-- but WITHOUT ANY WARRANTY; without even the implied warranty of MERCHAN-  --
-- TABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU General Public --
-- License  for more details. You  should  have  received a copy of the GNU --
-- General Public License  distributed with GNAT; see file COPYING. If not, --
-- write to the Free Software Foundation,  51 Franklin Street, Fifth Floor, --
-- Boston,                                                                  --
--                                                                          --
-- gnat2why is maintained by AdaCore (http://www.adacore.com)               --
--                                                                          --
------------------------------------------------------------------------------

with Why.Types;          use Why.Types;
with Why.Atree.Builders; use Why.Atree.Builders;
with Why.Atree.Mutators; use Why.Atree.Mutators;
with Why.Atree.Tables;   use Why.Atree.Tables;
with Why.Gen.Consts;     use Why.Gen.Consts;
with Why.Gen.Decl;       use Why.Gen.Decl;
with Gnat2Why.Locs;      use Gnat2Why.Locs;
with Why.Gen.Names;      use Why.Gen.Names;

package body Why.Gen.Preds is

   generic
      type Element_Type is private;
      type Chain_Type is array (Positive range <>) of Element_Type;

      with procedure Chain_Set (Root, Element : Element_Type);

   function Finalize_Chain
     (Chain : Chain_Type;
      Tail  : Element_Type)
     return Element_Type;
   --  Same as New_Predicate_Body and New_Universal_Predicate_Body,
   --  for any type that can be "chained"; this function is used to factorize
   --  out the body of these two functions.

   -------------------------
   -- Define_Eq_Predicate --
   -------------------------

   procedure Define_Eq_Predicate
     (File : W_File_Id;
      Name : String)
   is
      --  Identifiers
      X_S               : constant String := "x";
      Y_S               : constant String := "y";

      --  predicate eq___<name> (x : <name>, y : <name>) = [...]
      Pred_Name         : constant W_Identifier_Id := Eq_Pred_Name (Name);
      X_Binder          : constant W_Logic_Binder_Id :=
                            New_Logic_Binder
                            (Name       => New_Identifier (X_S),
                             Param_Type => New_Abstract_Type
                             (Name => New_Identifier (Name)));
      Y_Binder          : constant W_Logic_Binder_Id :=
                            New_Logic_Binder
                            (Name       => New_Identifier (Y_S),
                             Param_Type => New_Abstract_Type
                             (Name => New_Identifier (Name)));

      --  integer_of___<name> (x) = integer_of___<name> (y)
      Conversion        : constant W_Identifier_Id :=
                            New_Conversion_To_Int (Name);
      X_To_Base_Type_Op : constant W_Term_Id :=
                            New_Operation
                              (Name       => Conversion,
                               Parameters => (1 => +New_Term (X_S)));
      Y_To_Base_Type_Op : constant W_Term_Id :=
                            New_Operation
                              (Name =>
                                 +Duplicate_Any_Node (Id => +Conversion),
                               Parameters => (1 => +New_Term (Y_S)));
   begin
      --  ...now set the pieces together:
      New_Predicate_Definition
         (File    => File,
          Name    => Pred_Name,
          Binders => (1 => X_Binder, 2 => Y_Binder),
          Def     =>
            New_Equal (X_To_Base_Type_Op, Y_To_Base_Type_Op));
   end Define_Eq_Predicate;

   ----------------------------
   -- Define_Range_Predicate --
   ----------------------------

   procedure Define_Range_Predicate
     (File  : W_File_Id;
      Name  : String;
      First : Uint;
      Last  : Uint)
   is
      --  Identifiers
      Arg_S      : constant String := "x";
      First_S    : constant String := "first";
      Last_S     : constant String := "last";

      --  predicate <name>___in_range (x : int) = [...]
      Pred_Name  : constant W_Identifier_Id := Range_Pred_Name (Name);
      Binder     : constant W_Logic_Binder_Id :=
                     New_Logic_Binder (Name       => New_Identifier (Arg_S),
                                       Param_Type => New_Type_Int);

      --  let first = <first> in
      --  let last  = <last>  in [...]
      Decl_First : constant W_Binding_Pred_Unchecked_Id :=
                     New_Binding_Pred (First_S, First);
      Decl_Last  : constant W_Binding_Pred_Unchecked_Id :=
                     New_Binding_Pred (Last_S, Last);

      --  first <= x <= last
      Context    : constant W_Predicate_Id :=
                     New_Related_Terms (Left   => +New_Term (First_S),
                                        Op     => New_Rel_Le,
                                        Right  => +New_Term (Arg_S),
                                        Op2    => New_Rel_Le,
                                        Right2 => +New_Term (Last_S));
      Pred_Body  : constant W_Predicate_Id :=
                     New_Predicate_Body ((Decl_First, Decl_Last), Context);
   begin
      New_Predicate_Definition
         (File    => File,
          Name    => Pred_Name,
          Binders => (1 => Binder),
          Def     => Pred_Body);
   end Define_Range_Predicate;

   --------------------
   -- Finalize_Chain --
   --------------------

   function Finalize_Chain
     (Chain : Chain_Type;
      Tail  : Element_Type)
     return Element_Type is
   begin
      for J in reverse Chain'Range loop
         if J = Chain'Last then
            Chain_Set (Chain (J), Tail);
         else
            Chain_Set (Chain (J), Chain (J + 1));
         end if;
      end loop;

      return Chain (Chain'First);
   end Finalize_Chain;

   ----------------------
   -- New_Binding_Pred --
   ----------------------

   function New_Binding_Pred
     (Name  : String;
      Value : Uint)
     return W_Binding_Pred_Unchecked_Id
   is
      Result : constant W_Binding_Pred_Unchecked_Id :=
                 New_Unchecked_Binding_Pred;
   begin
      Binding_Pred_Set_Name (+Result, +New_Identifier (Name));
      Binding_Pred_Set_Def (+Result, +New_Constant (Value));
      return Result;
   end New_Binding_Pred;

   function New_Conditional_Prop
      (Ada_Node : Node_Id := Empty;
       Condition : W_Predicate_Id;
       Then_Part : W_Predicate_Id;
       Else_Part : W_Predicate_Id) return W_Predicate_Id
   is
   begin
      return
         New_Conjunction
            (Ada_Node => Ada_Node,
             Left     =>
               New_Implication
                  (Ada_Node => Ada_Node,
                   Left     => Condition,
                   Right    => Then_Part),
             Right    =>
               New_Implication
                  (Ada_Node => Ada_Node,
                   Left     =>
                     New_Negation
                        (Ada_Node => Ada_Node,
                         Operand  => +Duplicate_Predicate (Id => +Condition)),
                   Right    => Else_Part));
   end New_Conditional_Prop;

   ---------------
   -- New_Equal --
   ---------------

   function New_Equal
     (Left : W_Term_Id;
      Right : W_Term_Id) return W_Predicate_Id
   is
   begin
      return New_Related_Terms
         (Left => Left,
          Right => Right,
          Op => New_Rel_Eq);
   end New_Equal;

   ---------------------------
   -- New_Located_Assertion --
   ---------------------------

   function New_Located_Assertion
      (Ada_Node : Node_Id;
       Pred     : W_Predicate_Id) return W_Assertion_Id
   is
   begin
      return
        New_Assertion
          (Ada_Node => Ada_Node,
           Pred     =>
             New_Located_Predicate
               (Ada_Node => Ada_Node,
                Pred     => Pred));
   end New_Located_Assertion;

   ---------------------------
   -- New_Located_Predicate --
   ---------------------------

   function New_Located_Predicate
      (Ada_Node : Node_Id;
       Pred     : W_Predicate_Id) return W_Predicate_Id
   is
   begin
      return
         New_Named_Predicate
           (Ada_Node => Ada_Node,
            Name     => New_Located_Label (Ada_Node),
            Pred     => Pred);
   end New_Located_Predicate;

   ----------------
   -- New_NEqual --
   ----------------

   function New_NEqual
     (Left : W_Term_Id;
      Right : W_Term_Id) return W_Predicate_Id
   is
   begin
      return New_Related_Terms
         (Left => Left,
          Right => Right,
          Op => New_Rel_Ne);
   end New_NEqual;

   ------------------------
   -- New_Predicate_Body --
   ------------------------

   function New_Predicate_Body
     (Bindings : Binding_Pred_Chain;
      Context  : W_Predicate_Id)
     return W_Predicate_Id
   is
      procedure Set_Context
        (Root, Element : W_Predicate_Unchecked_Id);

      function Finalize_Binding_Chain is
        new Finalize_Chain
        (Element_Type => W_Predicate_Unchecked_Id,
         Chain_Type   => Binding_Pred_Chain,
         Chain_Set    => Set_Context);

      -----------------
      -- Set_Context --
      -----------------

      procedure Set_Context
        (Root, Element : W_Predicate_Unchecked_Id) is
      begin
         Binding_Pred_Set_Context (Root, +Element);
      end Set_Context;

   begin
      return +Finalize_Binding_Chain (Bindings, +Context);
   end New_Predicate_Body;

   --------------------
   -- New_Rel_Symbol --
   --------------------

   function New_Rel_Symbol (Symbol : W_Relation) return W_Relation_Id
   is
   begin
      case Symbol is
         when W_Rel_Gt => return New_Rel_Gt;
         when W_Rel_Lt => return New_Rel_Lt;
         when W_Rel_Eq => return New_Rel_Eq;
         when W_Rel_Ge => return New_Rel_Ge;
         when W_Rel_Le => return New_Rel_Le;
         when W_Rel_Ne => return New_Rel_Ne;
      end case;
   end New_Rel_Symbol;

   ---------------------------
   -- New_Simpl_Conjunction --
   ---------------------------

   function New_Simpl_Conjunction (Left, Right : W_Predicate_Id)
      return W_Predicate_Id
   is
   begin
      if Get_Kind (+Left) = W_True_Literal_Pred then
         return Right;
      elsif Get_Kind (+Right) = W_True_Literal_Pred then
         return Left;
      else
         return New_Conjunction (Left => Left, Right => Right);
      end if;
   end New_Simpl_Conjunction;

   ----------------------------------
   -- New_Universal_Predicate_Body --
   ----------------------------------

   function New_Universal_Predicate_Body
     (Foralls : Universal_Quantif_Chain;
      Context : W_Predicate_Id)
     return W_Predicate_Id
   is
      procedure Set_Pred (Root, Element : W_Universal_Quantif_Unchecked_Id);

      function Finalize_Univ_Chain is
        new Finalize_Chain
        (Element_Type => W_Universal_Quantif_Unchecked_Id,
         Chain_Type   => Universal_Quantif_Chain,
         Chain_Set    => Set_Pred);

      --------------
      -- Set_Pred --
      --------------

      procedure Set_Pred (Root, Element : W_Universal_Quantif_Unchecked_Id) is
      begin
         Universal_Quantif_Set_Pred (Root, +Element);
      end Set_Pred;

   begin
      return +Finalize_Univ_Chain (Foralls, +Context);
   end New_Universal_Predicate_Body;

end Why.Gen.Preds;
