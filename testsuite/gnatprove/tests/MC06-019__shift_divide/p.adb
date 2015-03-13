package body P
  with SPARK_Mode => On
is

   procedure Op1 (A : in out U.U32)
   is
   begin
      A := U.Shift_Right (A, 2);
   end Op1;

   procedure Op2 (A : in out U.U32)
   is
   begin
      A := U.Shift_Right (A, 17);
   end Op2;

end P;
