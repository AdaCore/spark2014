package tq is

   type Complex is record
      mReal : Integer;
      mImaginary : Integer;
   end record;

   procedure Affectation (P, Q : out Complex);

end tq;

