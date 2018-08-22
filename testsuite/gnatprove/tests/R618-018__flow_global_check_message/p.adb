package body P with Refined_State => (State1 => A,
                                      State2 => B,
                                      State3 => (C, D, E))
is
   A : Integer := 2;
   B : Integer := 4;
   C, D, E : Integer := 0;

   procedure Proc1
     with Refined_Global => A
   is
      C : Integer;
   begin
      if B > 0 then
         C := A;
      else
         C := 0;
      end if;
   end Proc1;

   procedure Proc2
     with Refined_Depends => (A => null)
   is
   begin
      A := B;
   end Proc2;

   procedure Proc3
     with Refined_Global => (C, D)
   is
   begin
      if C = D and D = E then
         null;
      end if;
   end Proc3;

   procedure Proc4
     with Refined_Depends => (C => D)
   is
   begin
      C := D + E;
   end Proc4;

   procedure Proc5
     with Refined_Depends => (A => A)
   is
   begin
      A := A;
      B := A;
   end Proc5;

   procedure Proc6
     with Refined_Global => (In_Out => A)
   is
   begin
      A := A;
      B := A;
   end Proc6;

end P;
