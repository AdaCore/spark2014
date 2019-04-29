package Exp_Le_Last
   with SPARK_Mode
is

   generic
      type Element_Type is (<>);
   procedure Foo (Offset : Natural) with
      Pre => Element_Type'Size <= 2 ** 62;

end Exp_Le_Last;
