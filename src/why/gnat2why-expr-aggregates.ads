------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--               G N A T 2 W H Y - E X P R - A G G R E G A T E S            --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                     Copyright (C) 2023-2026, AdaCore                     --
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

with SPARK_Definition.Annotate; use SPARK_Definition.Annotate;

package Gnat2Why.Expr.Aggregates is

   function Transform_Array_Aggregate
     (Params        : Transformation_Params;
      Domain        : EW_Domain;
      Expr          : N_Aggregate_Kind_Id;
      Update_Prefix : Opt_N_Subexpr_Id := Empty;
      Relaxed_Init  : Boolean) return W_Expr_Id;
   --  Transform an aggregate Expr of array type. The aggregate may be a plain
   --  array aggregate (Ada RM 4.3.3), an array delta aggregate (Ada RM 4.3.4),
   --  or a multi-dimensional delta array aggregate defined by a 'Update
   --  attribute (GNAT extension). The aggregate is delta iff there is a
   --  non-empty update prefix supplied, in which case only the updates are
   --  looked up in Expr. Relaxed_Init identify whether the resulting array
   --  should have relaxed initialization.
   --
   --  The core translation is to produce a Why3 proposition P that defines the
   --  aggregate value by stating what its components and bounds are. The
   --  subexpressions of the aggregate, its 'elements', are separated out of
   --  the aggregate through the use of intermediate Why3 variables. This is
   --  done whenever such separation is possible (for components under iterated
   --  component association, elements depends on index, so they cannot be
   --  defined once and for all ahead of time). For example, for aggregate:
   --
   --  A : array (B .. B + 3) of Integer :=
   --    (1 => V + 3, 2 => V + 4, others => K - 1)
   --
   --  the defining proposition is generated along the lines of:
   --
   --  def_prop a f l x y z :=
   --      a.__first = f /\ a.__last = l /\ get a 1 = x /\ get a 2 = y
   --         /\ (forall i. i <> 1 /\ i <> 2 -> get a i = z)
   --
   --  With a being a variable standing for the defined value, and x,y,z,f,l
   --  being free variables standing for the translation of components (x,y,z
   --  for subexpressions V + 3, V + 4, K-1 respectively) and bounds (f,l for
   --  lower and upper bounds B, B+3 respectively). In general, the proposition
   --  will contain additional guards for bounds/indexes to ensures it has a
   --  witness (a) for every instance of the elements (x,y,z,f,l). That is,
   --  (forall x y z f l. exists a. def_prop a f l x y z) should be justified
   --  at the meta level for the translation to be sound.
   --
   --  As an alternative to the conjunctive structure above, the components of
   --  the aggregate can be described for an arbitrary index by a succession of
   --  ifs (a mix of conjunctive structure and successive if may occur for
   --  multidimensional arrays). This is necessary for delta aggregates, due to
   --  updated choices being allowed to overlap (possibly dynamically). For
   --  example, the following delta aggregate is allowed:
   --
   --  (U with delta I .. J => X, K => Y)
   --
   --  And the defining proposition (about result array a) is:
   --
   --  def_prop a u i j k x y :=
   --    a.__first = u.__first /\ a.__last = u.__last /\
   --    (forall index. if index = k then get a index = y else
   --                   if i <= index <= j then get a index = x else
   --                   get a index = get u index)
   --
   --  The translation may be called multiple times on the same Ada node,
   --  corresponding to different phases. If all elements of Expr can be
   --  properly separated away (that is, there is no iterated component
   --  association), a logic function aggr_func is generated and stored in the
   --  E_Module for Expr. That function is axiomatized (in the corresponding
   --  axiom module) as returning a witness for the defining proposition for
   --  every instance of the elements, taken as parameters.
   --
   --  function aggr_func <element-types> : <type of aggregate>
   --
   --  axiom aggr_func_def : forall <element-vars>:<element-types>.
   --    let a = aggr_func <element-vars> in def_prop a <element-vars>
   --    (* def_prop inline, we do not make a predicate symbol *)
   --
   --  The aggregate is then translated by a call to aggr_func, preceded in the
   --  program domain by the various checks expected for the aggregate.
   --
   --  If there are iterated component associations, instead, the expression is
   --  completely processed every time to translate components under iterated
   --  association properly. The components cannot be replaced by variables as
   --  they depend on the iteration index.
   --  The translation in the program domain replace the function call by an
   --  any statement:
   --
   --  let <element-vars> = <element-values> in
   --  ... (* Checks *) ...;
   --  any { def_prop result <element-vars> } (* In place of call *)
   --
   --  The translation in the term domain produces a Why3 epsilon:
   --
   --  let <element-vars> = <element-values> in
   --  (epsilon A. def_prop result <element-vars>) (* In place of call *)
   --
   --  A function call could be used if we processed components under iterated
   --  component associations to find the actual variable content and replaced
   --  it by additional elements. For example, for aggregate:
   --
   --  (for I in 1 .. 42 => H (I, G(X,X)))
   --
   --  We produce defining proposition:
   --
   --  def_prop a :=
   --    a.__first = 1 /\ a.__last = 42
   --    /\ (forall i. get A i = 'H' i ('G' 'X' 'X'))
   --
   --  Which is only meaningful in a context where reference to variable 'X'
   --  make sense (so not in axioms). This could be turned into a format
   --  suitable for the function-based translation if we took X through an
   --  additional parameter. This is effectively what Why3 does when
   --  eliminating epsilon on its end, but it would be more error-prone to do
   --  so ahead of time due to the variety of contextual elements (variables,
   --  but also reference to 'Old, 'Loop_Entry, @, etc.), and the need to
   --  correctly replace them by element variables during translation. In
   --  contrast, Why3's epsilon elimination is a standalone pass which only
   --  have to deal with substitution of free variables in logic terms. We
   --  still make the effort of generating the function ourselves when it is
   --  reasonably easy to do so, because relying on Why3's epsilon elimination
   --  result in one function symbol per epsilon instead of a single global
   --  one, resulting in possibly lost sharing.

   function Generate_VCs_For_Aggregate_Annotation
     (E : Type_Kind_Id) return W_Prog_Id
   with Pre => Has_Aggregate_Annotation (E);
   --  Generate checks for the initialization and the preservation of the
   --  invariants used to model aggregates.

   function Transform_Container_Aggregate
     (Expr : Node_Id; Params : Transformation_Params; Domain : EW_Domain)
      return W_Expr_Id;
   --  Generate the translation of a container aggregate. It is done similarly
   --  to array aggregates. A logic function is generated along with an axiom,
   --  and the aggregate is translated as a function call.

   function Transform_Deep_Delta_Aggregate
     (Expr : Node_Id; Domain : EW_Domain; Params : Transformation_Params)
      return W_Expr_Id;
   --  Transform a deep delta aggregate. It is translated directly as a record
   --  update if it contains only record components. Otherwise, a logic
   --  function is generated along with an axiom, and the aggregate is
   --  translated as a function call.

end Gnat2Why.Expr.Aggregates;
