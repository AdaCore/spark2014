package body Other
  with SPARK_Mode => Off
is
   Hidden_Var : Integer := 0;

   type My_Range is new Integer range Hidden_Var .. Max;

   function Foo return Integer is
      (Integer (My_Range'Last) - Integer (My_Range'First) + 1);
end Other;
