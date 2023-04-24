procedure Main with SPARK_Mode is

   type R1 (Pos : Boolean) is record
      V : Integer;
   end record;
   subtype R2 is R1 with Predicate => R2.Pos = (R2.V > 0);
   type T1 is access all R1;
   type T2 is access all R2;

   X : T1;
begin
   pragma Assert (T2 (X) = null);
end Main;
