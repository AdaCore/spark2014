package body Pkg_A
  with Refined_State => (State_A => A,
                         State_B => (B, C))
is


   A : Integer;        --  error: not initialized
   B : Integer;
   C : Integer := 12;  --  error: ineffective

   function Do_Something (X : Integer) return Integer is (X * 2)
     with Pre => X in -100 .. 100;

begin

   Z := Do_Something (X);   --  error: use of uninitialized X
   W := 12;                 --  error: ineffective
   Q := 42;

end Pkg_A;
