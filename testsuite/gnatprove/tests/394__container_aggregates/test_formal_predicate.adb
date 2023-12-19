with Test_Formal_Predicate_Instances; use Test_Formal_Predicate_Instances;

procedure Test_Formal_Predicate with SPARK_Mode is

   procedure Test_Lists with Global => null is
      use My_Lists;
      X : My_Lists.List := [R(1), R(Get_Value), R(3)];  -- @PREDICATE_CHECK:FAIL
   begin
      null;
   end Test_Lists;

   procedure Test_Hashed_Maps (K : Natural) with Global => null is
      use My_HMaps;
      X : My_HMaps.Map := [1 => R(1), 2 => R(Get_Value), 3 => R(3)];  -- @PREDICATE_CHECK:FAIL
   begin
      null;
   end Test_Hashed_Maps;

   procedure Test_Hashed_Sets (E : Natural) with Global => null is
      use My_HSets;
      X : My_HSets.Set := [R(1), R(2), R(Get_Value)];  -- @PREDICATE_CHECK:FAIL
   begin
      null;
   end Test_Hashed_Sets;

   procedure Test_Ordered_Maps with Global => null is
      use My_OMaps;
      X : My_OMaps.Map := [1 => R(Get_Value), 2 => R(2), 3 => R(3)];  -- @PREDICATE_CHECK:FAIL
   begin
      null;
   end Test_Ordered_Maps;

   procedure Test_Ordered_Sets with Global => null is
      use My_OSets;
      X : My_OSets.Set := [R(1), R(2), R(Get_Value)];  -- @PREDICATE_CHECK:FAIL
   begin
      null;
   end Test_Ordered_Sets;

   procedure Test_Vectors with Global => null is
      use My_Vectors;
      X : My_Vectors.Vector := [R(1), R(Get_Value), R(3)];  -- @PREDICATE_CHECK:FAIL
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
end Test_Formal_Predicate;
