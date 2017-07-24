package body P
  with Refined_State => (State_A => A,
                         State_B => B)
is
   A : Integer;
   B : Integer;

   procedure Proc (X : Integer;
                   Y : Integer)
   is
   begin
      B := Y;
   end Proc;

end P;
