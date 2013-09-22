with Generic_Float_Tests;

package Foo
  with SPARK_Mode
is

   pragma Elaborate_Body (Foo);

   package Float_Tests is new Generic_Float_Tests
     (FT                        => Float,
      Biggest_Representable_Int => Float (2 ** 24),
      Nextup_One                => 1.0000001);

   package Double_Tests is new Generic_Float_Tests
     (FT                        => Long_Float,
      Biggest_Representable_Int => Long_Float (2 ** 53),
      Nextup_One                => 1.00000000000000022204460492503);

end Foo;
