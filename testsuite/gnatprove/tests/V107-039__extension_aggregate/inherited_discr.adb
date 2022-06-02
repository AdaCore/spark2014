procedure Inherited_Discr with SPARK_Mode, Annotate => (GNATprove, Always_Return) is

   function Id (X : Integer) return Integer is (X);

   package P1 is
      type R (D : Integer) is tagged record
         X : Integer;
         Y : Positive;
      end record;
      function F return R;
      V : constant R := (D => 1, X => 0, Y => Id (2));
   end P1;

   package body P1 is
      function F return R is ((V with delta Y => 10 / V.Y));
   end P1;

   package Q1 is
      use P1;
      type T1 is new R (D => 0) with null record;
      function F return T1 is (R'(F) with null record); --@DISCRIMINANT_CHECK:FAIL
      W : constant T1 := (D => 0, X => 1, Y => 2);
   end Q1;
begin
   null;
end Inherited_Discr;
