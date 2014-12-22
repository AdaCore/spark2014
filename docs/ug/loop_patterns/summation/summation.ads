package Summation
  with SPARK_Mode
is
   Max_Sum : constant Natural := Natural'Last;
   Max_Index : constant Natural := 1000;
   Max_Val : constant Natural := Max_Sum / Max_Index;

   subtype Index_T is Natural range 1 .. Max_Index;

   subtype Component_T is Natural range 0 .. Max_Val;

   type Ar is array (Index_T) of Component_T;

   procedure Sum (A : in Ar; S: out Natural) with
     Post => S <= Max_Val * Max_Index;

end Summation;
