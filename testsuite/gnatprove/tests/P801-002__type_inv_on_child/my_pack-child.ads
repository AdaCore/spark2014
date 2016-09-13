package My_Pack.Child with SPARK_Mode is
   type T2 is private;

   function Incr (X : T) return T;
private
   type T2 is new T;

   function Incr (X : T) return T is (X + 1);
end My_Pack.Child;
