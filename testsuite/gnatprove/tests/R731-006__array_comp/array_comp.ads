package Array_Comp with SPARK_Mode is
   type Nat_Array is array (Positive range <>) of Natural;

   XX : Nat_Array := (1 => 1, 2 => 0);

   YY : Nat_Array := (1 => 1, 2 => 0, 3 => 1);

   pragma Assert (YY (1 .. 2) < XX);
end Array_Comp;
