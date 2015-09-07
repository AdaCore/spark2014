package Interval
  with SPARK_Mode => On
is
   type Interval is private
     with
       Type_Invariant => Has_Valid_Order(Interval);

   function Make(Low, High : Float) return Interval;

   function Has_Valid_Order(Int : Interval) return Boolean;

private
   type Interval is
      record
         Low  : Float;
         High : Float;
      end record;

   function Has_Valid_Order(Int : Interval) return Boolean is (Int.Low <= Int.High);
end Interval;
