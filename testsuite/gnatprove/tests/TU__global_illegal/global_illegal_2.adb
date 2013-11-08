package body Global_Illegal_2
  with SPARK_Mode,
       Refined_State => (A => (X, Y))
is
   X, Y : Integer;
   Z    : constant Integer := 0;

   procedure P1 (Par1 : Integer)
     --  TU: 5. The Global aspect may only be specified for the initial
     --  declaration of a subprogram (which may be a declaration, a body or a
     --  body stub).
     with Global => (Output => X)
   is
   begin
      X := Par1;
   end P1;


   procedure P2 (Par1 : out Integer)
     --  TU: 8. A ``global_item`` shall not denote a state abstraction whose
     --  refinement is visible. [A state abstraction cannot be named within
     --  its enclosing package's body other than in its refinement. Its
     --  constituents must be used rather than the state abstraction.]
     with Global => (Input => A)
   is
   begin
      Par1 := X + Y;
   end P2;


   procedure P3 (Par1 : out Integer)
     with Global => (Input => (X, Y))
   is
      procedure Nested_P
        --  TU: 12. If a subprogram is nested within another and if the
        --  ``global_specification`` of the outer subprogram has an entity
        --  denoted by a ``global_item`` with a ``mode_specification`` of
        --  Input or the entity is a formal parameter with a mode of **in**,
        --  then a ``global_item`` of the ``global_specification`` of the
        --  inner subprogram shall not denote the same entity with a
        --  ``mode_selector`` of In_Out or Output.
        with Global => (Output => X,
                        In_Out => Y)
      is
      begin
         X := 5;
         Y := Y + 5;
      end Nested_P;
   begin
      Nested_P;
      Par1 := X + Y;
   end P3;


   procedure P4 (Par1 : out Integer)
     --  TU: 7. A ``global_item`` shall not denote a constant object other than
     --  a formal parameter [of an enclosing subprogram] of mode **in**.
     with Global => Z
   is
   begin
      Par1 := Z;
   end P4;
end Global_Illegal_2;
