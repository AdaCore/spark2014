private package My_Pack.Child_Bad with SPARK_Mode is

   function Incr_Priv (X : T) return T is (X + 1); --@INVARIANT_CHECK:NONE

   type T1 is private;

   function Incr (X : T1) return T1; --@INVARIANT_CHECK:FAIL

private
   type T1 is new Integer with Type_Invariant => T1 /= 0; --@INVARIANT_CHECK_ON_DEFAULT_VALUE:FAIL

   function Incr (X : T1) return T1 is (X + 1);
end My_Pack.Child_Bad;
