package Opers with
  SPARK_Mode
is

   generic
      type T is private;
      with function "+" (X, Y : T) return T is <>;
   function Apply_To_Self (X : T) return T;

   procedure Test (A : in out Integer);

end Opers;
