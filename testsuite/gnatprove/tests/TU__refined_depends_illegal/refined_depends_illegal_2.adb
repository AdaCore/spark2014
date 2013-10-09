package body Refined_Depends_Illegal_2
  with SPARK_Mode,
       Refined_State => (State => (X, Y))
is
   X, Y : Integer := 0;

   procedure P1 (Par : out Integer)
     with Refined_Depends => (Par => X)
   is
   begin
      Par := X + Y;  --  Illegal. Par depends only on X
   end P1;


   procedure P2 (Par : Integer)
     with Refined_Global  => (Output => (X, Y)),
          Refined_Depends => (X => Par,
                              Y => null)
   is
   begin
      Y := Par;  --  Illegal. Y depends on null
      X := 1 + Par;
   end P2;
end Refined_Depends_Illegal_2;
