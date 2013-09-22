generic
   type FT is digits <>;
   Biggest_Representable_Int : FT;
package Generic_Interval_Tests
  with SPARK_Mode
is
   pragma Elaborate_Body (Generic_Interval_Tests);
end Generic_Interval_Tests;
