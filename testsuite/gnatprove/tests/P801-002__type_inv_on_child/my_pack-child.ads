package My_Pack.Child with SPARK_Mode is
   type T2 is private;

   function Incr (X : T) return T; --@INVARIANT_CHECK:FAIL
private
   type T2 is new T;

   function Incr (X : T) return T is (X + 1);

   function Incr_Priv (X : T) return T is (X + 1); --@INVARIANT_CHECK:NONE
end My_Pack.Child;
