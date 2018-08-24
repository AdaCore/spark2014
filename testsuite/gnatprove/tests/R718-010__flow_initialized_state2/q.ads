package Q with SPARK_Mode
is
   type T is private with Default_Initial_Condition;
private
   pragma SPARK_Mode (Off);
   type T is new Integer;
end Q;
