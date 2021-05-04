private package My_Pack.Child_Bad with SPARK_Mode is
   type T1 is private;
private
   type T1 is new Integer with Type_Invariant => T1 /= 0;
end My_Pack.Child_Bad;
