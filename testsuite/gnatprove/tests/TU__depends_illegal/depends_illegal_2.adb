package body Depends_Illegal_2
  with SPARK_Mode,
       Refined_State => (A => (X, Y))
is
   X, Y : Natural;


   procedure P1 (Par1 : in Natural)
     --  TU: 2. The Depends aspect shall only be specified for the initial
     --  declaration of a subprogram (which may be a declaration, a body or a
     --  body stub).
     with Depends => ((X, Y) =>+ Par1)
   is
   begin
      X := X + Par1;
      Y := Par1 + Y - 1;
   end P1;


   procedure P2
     --  TU: 26. If only part of an entire object or state abstraction (only
     --  some of its constituents) is updated then the updated entity is
     --  dependent on itself as the parts that are not updated have their
     --  current value preserved. [Where a constituent of a state
     --  abstraction is updated but the refinement of the state abstraction
     --  is not visible, it is not known if all of the constituents have
     --  been updated by the subprogram and in such cases the the update is
     --  represented as the the update of the encapsulating state
     --  abstraction with a self dependency.]
     with Refined_Global  => (Output => X),
          Refined_Depends => (X => null)
   is
   begin
      X := 5;
   end P2;

   function F1 (Par1 : Natural) return Natural
     --  TU: 3. An ``input`` or ``output`` of a ``dependency_relation`` shall
     --  not denote a state abstraction whose refinement is visible [a state
     --  abstraction cannot be named within its enclosing package's body other
     --  than in its refinement].
     with Global  => A,
          Depends => (F1'Result => A,
                      null      => Par1)
   is
   begin
      return X;
   end F1;
end Depends_Illegal_2;
