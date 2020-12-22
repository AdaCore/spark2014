package Visibility with SPARK_Mode is

   type Int is private;

private

   pragma SPARK_Mode (Off);

   function Infinite_Loop2 return Boolean;

   type Int is new Integer with Type_Invariant => Infinite_Loop2;

end Visibility;
