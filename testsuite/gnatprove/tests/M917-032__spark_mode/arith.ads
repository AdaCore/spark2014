package Arith with SPARK_Mode => On is

   function Sum (X, Y : Integer) return Integer with SPARK_Mode => Off;

   function Sum_Ok (X, Y : Integer) return Boolean is
      (if X > 0 then Y <= Integer'Last - X else Y >= Integer'First - X);

   function Sum2 (X, Y : Integer) return Integer with SPARK_Mode => Off,
     Pre  => Sum_Ok (X, Y),
     Post => Sum2'Result = X + Y;

   subtype Index is Integer range 1 .. 10;
   type Int_Array is array (Index) of Integer;

   function Sum_Array (X, Y : Int_Array) return Int_Array with SPARK_Mode => On;

   function Sum_Array2 (X, Y : Int_Array) return Int_Array with SPARK_Mode => Off,
     Pre  => (for all J in Index => Sum_Ok (X(J), Y(J))),
     Post => (for all J in Index => Sum_Array2'Result(J) = X(J) + Y(J));

end Arith;
