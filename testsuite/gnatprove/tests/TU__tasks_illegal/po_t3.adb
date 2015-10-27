package body PO_T3
  with Refined_State => (State => Hidden)
is
   --  TU: 3. If a variable or a package which declares a state abstraction is
   --  declared immediately within the same declarative region as a
   --  ``single_task_declaration`` or a ``single_protected_declaration``, then
   --  the Part_Of aspect of the variable or state abstraction may denote the
   --  task or protected unit. This indicates that the object or state
   --  abstraction is not part of the visible state or private state of its
   --  enclosing package. [Loosely speaking, flow analysis will treat the
   --  object as though it were declared within its "owner". This can be useful
   --  if, for example, a protected object's operations need to reference an
   --  object whose Address aspect is specified.  The protected (as opposed to
   --  task) case corresponds to the previous notion of "virtual protected"
   --  objects in RavenSPARK.]
   --  An object or state abstraction which "belongs" to a task unit in this
   --  way is treated as a local object of the task (e.g., it cannot be named
   --  in a Global aspect specification occurring outside of the body of the
   --  task unit, just as an object declared immediately within the task body
   --  could not be).  An object or state abstraction which "belongs" to a
   --  protected unit in this way is treated as a component of the (anonymous)
   --  protected type (e.g., it can never be named in any Global aspect
   --  specification, just as a protected component could not be). [There is
   --  one obscure exception to these rules, described in the next paragraph: a
   --  subprogram which is declared within the statement list of the body of
   --  the immediately enclosing package (this is possible via a block
   --  statement).]
   --  The notional equivalences described above break down in the case of
   --  package elaboration.  The presence or absence of such a Part_Of aspect
   --  specification is ignored in determining the legality of an Initializes
   --  or Initial_Condition aspect specification.  [Very roughly speaking, the
   --  restrictions implied by such a Part_Of aspect specification are not
   --  really "in effect" during library unit elaboration; or at least that's
   --  one way to view it. For example such an object can be accessed from
   --  within the elaboration code of its immediately enclosing package. On the
   --  other hand, it could not be accessed from within a subprogram unless the
   --  subprogram is declared within either the task unit body in question (in
   --  the task case) or within the statement list of the body of the
   --  immediately enclosing package (in either the task or the protected
   --  case).]

   protected P_Int is
      function Get return Integer;

      entry Set (X : Integer);
   private
      The_Protected_Int : Integer := 0;
      Condition         : Boolean := True;
   end P_Int;

   Hidden : Integer := 5
     with Part_Of => P_Int;
   --  The above is illegal because Hidden is a constituent of State.

   protected body P_Int is
      function Get return Integer is
         (if The_Protected_Int >= 0
          then The_Protected_Int
          else The_Protected_Int + 10);

      entry Set (X : Integer) when Condition is
      begin
         The_Protected_Int := X + Hidden;
      end Set;
   end P_Int;

begin
   P_Int.Set (-10);
   pragma Assert (P_Int.Get = 5);
end PO_T3;
