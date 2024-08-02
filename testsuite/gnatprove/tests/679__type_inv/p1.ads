package P1 is
   type I is private;
private
   type I is new Integer with Type_Invariant => I /= 0, Default_Value => 1;
end P1;
