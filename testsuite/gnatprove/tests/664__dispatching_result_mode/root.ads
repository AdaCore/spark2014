package Root with SPARK_Mode is

   package Inner with SPARK_Mode => Off is
      type Hidden_Integer is new Integer;
   end Inner;

   type T is tagged null record;
   function Make (H : Inner.Hidden_Integer) return T
     with SPARK_Mode => Off, Import;
   function Make2 return T with SPARK_Mode => Off, Import;

end Root;
