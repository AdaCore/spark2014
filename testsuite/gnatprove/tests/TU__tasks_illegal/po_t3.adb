package body PO_T3
  with Refined_State => (State => Hidden)
is
   --  3. If a variable or a package which declares a state abstraction is
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
