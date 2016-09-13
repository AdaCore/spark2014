package My_Pack with SPARK_Mode is
   type T is private;
private
   type T is new Integer with Type_Invariant => T /= 0;
end My_Pack;
