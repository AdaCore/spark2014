procedure Inherited with SPARK_Mode is

   package P1 is
      type R is tagged null record;
      function F return R;
      V : constant R := (null record);
   end P1;

   package body P1 is
      function F return R is (V);
   end P1;

   package Q1 is
      use P1;
      type T1 is new R with null record;
      W : constant T1 := (null record);
   end Q1;

   package P2 is
      type R is tagged record
         X : Integer;
      end record;
      function F return R;
      V : constant R := (X => 0);
   end P2;

   package body P2 is
      function F return R is (V);
   end P2;

   package Q2 is
      use P2;
      type T2 is new R with null record with Predicate => X > 0;
      W : constant T2 := (X => 1);
   end Q2;

   procedure Bad1 with Pre => True is
   begin
      pragma Assert (P1.R'Class (Q1.F) in P1.R); --@ASSERT:FAIL
   end Bad1;

   procedure Bad2 with Pre => True is
   begin
      pragma Assert (P2.R'Class (Q2.F).X = 0); --@PREDICATE_CHECK:FAIL
   end Bad2;
begin
   Bad1;
end Inherited;
