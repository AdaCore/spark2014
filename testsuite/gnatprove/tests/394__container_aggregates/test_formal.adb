with Test_Formal_Instances; use Test_Formal_Instances;

procedure Test_Formal with SPARK_Mode is

   procedure Test_Lists with Global => null is
      use My_Lists;
      X : My_Lists.List := [1, Get_Value, 3];  -- @RANGE_CHECK:FAIL
   begin
      null;
   end Test_Lists;

   procedure Test_Hashed_Maps (K : Natural) with Global => null is
      use My_HMaps;
      X : My_HMaps.Map := [1 => 1, 2 => Get_Value, 3 => 3];  -- @RANGE_CHECK:FAIL
   begin
      null;
   end Test_Hashed_Maps;

   procedure Test_Hashed_Sets (E : Natural) with Global => null is
      use My_HSets;
      X : My_HSets.Set := [1, 2, Get_Value];  -- @RANGE_CHECK:FAIL
   begin
      null;
   end Test_Hashed_Sets;

   procedure Test_Ordered_Maps with Global => null is
      use My_OMaps;
      X : My_OMaps.Map := [1 => Get_Value, 2 => 2, 3 => 3];  -- @RANGE_CHECK:FAIL
   begin
      null;
   end Test_Ordered_Maps;

   procedure Test_Ordered_Sets with Global => null is
      use My_OSets;
      X : My_OSets.Set := [1, 2, Get_Value];  -- @RANGE_CHECK:FAIL
   begin
      null;
   end Test_Ordered_Sets;

   procedure Test_Vectors with Global => null is
      use My_Vectors;
      X : My_Vectors.Vector := [1, Get_Value, 3];  -- @RANGE_CHECK:FAIL
   begin
      null;
   end Test_Vectors;

begin
   Test_Lists;
   Test_Hashed_Maps (1);
   Test_Hashed_Sets (1);
   Test_Ordered_Maps;
   Test_Ordered_Sets;
   Test_Vectors;
end Test_Formal;
