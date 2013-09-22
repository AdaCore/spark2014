with Generic_Interval_Tests;

package Bar
  with SPARK_Mode
is

   package Float_Tests is new Generic_Interval_Tests
     (FT                        => Float,
      Biggest_Representable_Int => Float (2 ** 24));

   package Double_Tests is new Generic_Interval_Tests
     (FT                        => Long_Float,
      Biggest_Representable_Int => Long_Float (2 ** 53));

end Bar;
