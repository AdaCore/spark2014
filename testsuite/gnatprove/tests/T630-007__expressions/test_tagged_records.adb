procedure Test_Tagged_Records with SPARK_Mode is
   type B is tagged record
      F : Integer;
      G : Integer;
   end record;
   subtype Not_Zero is B with Predicate => Not_Zero.F /= 0;

   function Rand (X : Integer) return Boolean with Import;

   X : B := (others => 0);
begin
   if Rand (1) then
      Not_Zero (X) := (others => 1);
   else
      Not_Zero (X) := (@ with delta F => 1);--@PREDICATE_CHECK:FAIL
   end if;
end Test_Tagged_Records;
