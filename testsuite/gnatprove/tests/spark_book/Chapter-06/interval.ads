package Interval
  with SPARK_Mode => On
is
   type Interval is private;

   function Make(Low, High : Float) return Interval;

private
   type Interval is
      record
         Low  : Float := 0.0;
         High : Float := 0.0;
      end record
     with
       Type_Invariant => Has_Valid_Order(Interval);

   function Has_Valid_Order(Int : Interval) return Boolean is (Int.Low <= Int.High);
end Interval;
