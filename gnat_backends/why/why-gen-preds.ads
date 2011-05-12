------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                        W H Y - G E N - P R E D S                         --
--                                                                          --
--                                 S p e c                                  --
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

with Types;                use Types;
with Uintp;                use Uintp;
with VC_Kinds;             use VC_Kinds;

with String_Utils;         use String_Utils;
with Why.Ids;              use Why.Ids;
with Why.Conversions;      use Why.Conversions;
with Why.Sinfo;            use Why.Sinfo;
with Why.Unchecked_Ids;    use Why.Unchecked_Ids;
with Why.Atree.Properties; use Why.Atree.Properties;

package Why.Gen.Preds is

   --  This package provides facilities to manipulate Why predicates

   procedure Define_Range_Predicate
     (File  : W_File_Id;
      Name  : String;
      First : Uint;
      Last  : Uint);
   --  Generate the definition of the range predicate for an integer type.
   --  This predicate is True when the int argument is in range First .. Last.

   procedure Define_Eq_Predicate
     (File : W_File_Id;
      Name : String);
   --  Generate the definition of the equality predicate for an integer type.
   --  This predicate is True when conversions to int are equal.

   function New_Binding_Pred
     (Name  : String;
      Value : Uint)
     return W_Binding_Pred_Unchecked_Id;
   --  Create a new binding for a predicate; the context is left empty.
   --  e.g. let <name> = <value> in <empty>

   function New_Conditional_Prop
      (Ada_Node : Node_Id := Empty;
       Condition : W_Predicate_Id;
       Then_Part : W_Predicate_Id;
       Else_Part : W_Predicate_Id) return W_Predicate_Id;
   --  We generate a formula of the form
   --    (Cond => Then_Part) and (not Cond => Else_Part)

   function New_Equal
     (Left : W_Term_Id;
      Right : W_Term_Id) return W_Predicate_Id;
   --  Create the predicate "Left = Right"

   function New_NEqual
     (Left : W_Term_Id;
      Right : W_Term_Id) return W_Predicate_Id;
   --  Create the predicate "Left <> Right"

   function New_Equal_Bool
     (Left : W_Term_Id;
      Right : W_Predicate_Id) return W_Predicate_Id;
   --  Create the formula "Left = true <-> Right".

   function New_Located_Predicate
      (Ada_Node : Node_Id;
       Pred     : W_Predicate_Id;
       Reason   : VC_Kind) return W_Predicate_Id;
   --  Build a predicate with a fresh label corresponding to the Ada_Node.

   function New_Rel_Symbol (Symbol : W_Relation) return W_Relation_Id;
   --  Return a fresh relation node, given a relation symbol

   type Binding_Pred_Chain is array (Positive range <>)
     of W_Binding_Pred_Unchecked_Id;
   --  Array of bindings with an empty context. Those are meant to be
   --  linked together in a predicate of the form:
   --
   --  let <my_chain_1_name> = <my_chain_1_value> in
   --  let <my_chain_2_name> = <my_chain_2_value> in
   --  [...]
   --  let <my_chain_n_name> = <my_chain_n_value> in
   --     <empty>

   function New_Predicate_Body
     (Bindings : Binding_Pred_Chain;
      Context  : W_Predicate_Id)
     return W_Predicate_Id with
     Pre => (Is_Root (+Context));
   --  Create a predicate by linking together the bindings and
   --  associating the context to them.

   function New_Simpl_Conjunction (Left, Right : W_Predicate_Id)
      return W_Predicate_Id;
   --  Build a conjunction, but check if we can simplify it  - one of the
   --  arguments may be "true".

   type Universal_Quantif_Chain is array (Positive range <>)
     of W_Universal_Quantif_Unchecked_Id;
   --  Array of universal quantifiers with an empty context. Those are meant
   --  to be linked together in a predicate of the form:
   --
   --  forall <my_chain_1_name> : <my_chain_1_type>.
   --  forall <my_chain_2_name> : <my_chain_2_type>.
   --  [...]
   --  forall <my_chain_n_type> : <my_chain_n_type>.
   --     <empty>

   function New_Universal_Predicate_Body
     (Foralls : Universal_Quantif_Chain;
      Context : W_Predicate_Id)
     return W_Predicate_Id with
     Pre => (Is_Root (+Context));
   --  Create a predicate by linking together the universal quantifiers and
   --  associating the context to them.

   function New_Universal_Predicate
     (Arg_Names : String_Lists.List;
      Logic     : W_Logic_Type_Id;
      Pred      : W_Predicate_Id)
     return W_Predicate_Id;
   --  Given a predicate, a logic of the form
   --
   --   t1, t2, ..., tn -> t
   --
   --  and a list of arg names
   --
   --   N1, N2, ..., Nn
   --
   --  create an universal quantification of the form:
   --
   --   forall N1 : t1.
   --   forall N2 : t2.
   --   [...]
   --   forall Nn : tn.
   --    <Pred>

end Why.Gen.Preds;
