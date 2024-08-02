package Privacy with SPARK_Mode is

   type T is tagged null record;
   type V is new T with private;
   type W is tagged private;

   --  Wrappers for Make should not come in SPARK_Mode, since it is
   --  neither a public primitive of V nor W.

private
   pragma SPARK_Mode (Off);
   type U is new T with null record;
   function Make return U is (null record);
   function Evil (X : U) return Integer is (0);
   type V is new U with null record;
   type W is new V with null record;

end Privacy;
