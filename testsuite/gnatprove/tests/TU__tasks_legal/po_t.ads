package PO_T
  with Abstract_State => State
is

   --  TU: 3. If a variable or a package which declares a state abstraction is
   --  declared immediately within the same declarative region as a
   --  ``single_task_declaration`` or a ``single_protected_declaration``, then
   --  the Part_Of aspect of the variable or state abstraction may denote the
   --  task or protected object. This indicates that the object or state
   --  abstraction is not part of the visible state or private state of its
   --  enclosing package. [Loosely speaking, flow analysis will treat the
   --  object as though it were declared within its "owner". This can be useful
   --  if, for example, a protected object's operations need to reference an
   --  object whose Address aspect is specified.  The protected (as opposed to
   --  task) case corresponds to the previous notion of "virtual protected"
   --  objects in RavenSPARK.]

   protected P_Int is
      function Get return Integer;

      entry Set (X : Integer);
   private
      The_Protected_Int : Integer := 0;
   end P_Int;

   Condition : Boolean := True
     with Part_Of => P_Int;

private

   protected Hidden_PO
     with Part_Of => State
   is
      function Get return Integer;

      entry Set (X : Integer);
   private
      The_Protected_Int : Integer := 0;
      Switch            : Boolean := True;
   end Hidden_PO;

end PO_T;
