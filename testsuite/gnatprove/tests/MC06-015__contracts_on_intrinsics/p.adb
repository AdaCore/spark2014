package body P
  with SPARK_Mode => On
is

   procedure Op1 (A : in out U.U32)
   is
   begin
      --  This should prove fine
      A := U.Shift_Right (A, 2); -- @PRECONDITION:PASS
   end Op1;

   procedure Op2 (A : in out U.U32)
   is
   begin
      --  Precondition violation
      A := U.Shift_Right (A, 17);
   end Op2;

end P;
