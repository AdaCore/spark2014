package Q is
   type T is private with Default_Initial_Condition;

private
   pragma Spark_Mode (Off);
   type T is new Integer with Default_Value => 0;
end Q;
