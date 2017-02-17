package Loopframe with
  SPARK_Mode
is

   type Idx is range 0 .. 5;
   subtype Valid_Idx is Idx range 1 .. 5;
   type Arr is array (Valid_Idx) of Boolean;

   A : Arr;

   function Get return Idx with
     Post => (if Get'Result /= 0 then A (Get'Result));

end Loopframe;
