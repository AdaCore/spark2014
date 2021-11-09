procedure Main with SPARK_Mode is
   function Rand (X : Integer) return Boolean with Import;
   function Id (X : Integer) return Integer is (X);

   type R is record
      F, G : Integer := 0;
   end record;

   subtype T is R with
     Predicate =>
       T.F >= 0
       and then T.G >= 0;

   subtype T2 is R with
     Predicate =>
       T2.F > 0
       and then T2.G >= 0;

   type Holder is record
      C : T := (F => 0, G => -1); --@PREDICATE_CHECK:FAIL
   end record;

   function F (X : Integer) return Boolean is
     (X <= 100
      and X >= -100);

   X : T;
begin
   if Rand (1) then
      X.F := -1; --@PREDICATE_CHECK:FAIL
   elsif Rand (2) then
      X.G := -1; --@PREDICATE_CHECK:FAIL
   elsif Rand (3) then
      pragma Assert (F (120)); --@ASSERT:FAIL
   elsif Rand (4) then
      pragma Assert (F (-120)); --@ASSERT:FAIL
   elsif Rand (5) then
      pragma Assert (R'(0, -1) in T); --@ASSERT:FAIL
   elsif Rand (6) then
      declare
         Y : T2; --@PREDICATE_CHECK:FAIL
      begin
         null;
      end;
   elsif Rand (7) then
      declare
         Y : Holder;
      begin
         null;
      end;
   end if;
end;
