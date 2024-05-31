package Q2 with SPARK_Mode is
   type T3 is private;
private
   type T3 is new Integer with Type_Invariant => T3 >= 0, Default_Value => 0;
end Q2;
