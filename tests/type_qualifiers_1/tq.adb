package body tq is

   procedure Affectation (P, Q : out Complex)
   is
   begin
      P := (mReal => 0, mImaginary => 1);
      Q := (mReal => 0, mImaginary => 1);
   end Affectation;

end tq;

