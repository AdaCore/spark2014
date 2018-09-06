package Q with SPARK_Mode
is
   type T1 (D : Integer) is private with Default_Initial_Condition;
   type T2 is private with Default_Initial_Condition;
private
   pragma SPARK_Mode (Off);
   type T1 (D : Integer) is record
      A : Integer := 0;
   end record;

   type T2 is record
      A : Integer := 0;
   end record;
end Q;
