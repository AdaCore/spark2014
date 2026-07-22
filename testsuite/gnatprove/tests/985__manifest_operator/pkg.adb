package body Pkg
  with SPARK_Mode
is
   function "&" (X, Y : T) return T
   is (T'Max (X, Y));

   function "-" (X, Y : T) return T
   is (T'Max (X, Y));

   function "-" (X : T) return T
   is (X);
end Pkg;
