package Q with SPARK_Mode
is
   type T (D : Integer) is private with Default_Initial_Condition;
private
   pragma SPARK_Mode (Off);
   type T (D : Integer) is record
      A : Integer := 0;
   end record;
end Q;
