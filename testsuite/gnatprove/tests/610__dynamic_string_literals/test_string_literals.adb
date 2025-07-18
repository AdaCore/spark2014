procedure Test_String_Literals with SPARK_Mode is
   function Id (X : Integer) return Integer is (X);

   procedure Test_Signed_Too_Big with Global => null is
      type Small_Int is new Integer range 1 .. Id (2);
      type My_String is array (Small_Int range <>) of Character;

      X : My_String := "foo"; --@RANGE_CHECK:FAIL
   begin
      null;
   end Test_Signed_Too_Big;

   procedure Test_Signed_Bad_Fst with Global => null is
      type Small_Int is new Integer range Id (12) .. 14;
      type My_String is array (Small_Int range <>) of Character;

      X : My_String (11 .. 13) := "foo"; --@RANGE_CHECK:FAIL
   begin
      null;
   end Test_Signed_Bad_Fst;

   type Mod_8 is mod 8;
   function Id (X : Mod_8) return Mod_8 is (X);

   procedure Test_Mod_Empty_1 with Global => null is
      type Small_Int is new Mod_8 range 1 .. 7;
      type My_String is array (Small_Int range <>) of Character;

      X : My_String := "";
   begin
      null;
   end Test_Mod_Empty_1;

   procedure Test_Mod_Empty_3 with Global => null is
      type Small_Int is new Mod_8 range Id (0) .. 7;
      type My_String is array (Small_Int range <>) of Character;

      X : My_String (1 .. 0) := ""; --@RANGE_CHECK:PASS
   begin
      null;
   end Test_Mod_Empty_3;

   procedure Test_Mod_Ok_2 with Global => null is
      type Small_Int is new Mod_8 range Id (0) .. 7;
      type My_String is array (Small_Int range <>) of Character;

      X : My_String (0 .. 2) := "foo"; --@RANGE_CHECK:PASS
   begin
      pragma Assert (X'First = 0); --@ASSERT:PASS
   end Test_Mod_Ok_2;

   procedure Test_Mod_Too_Big with Global => null is
      type Small_Int is new Mod_8 range 0 .. Id(1);
      type My_String is array (Small_Int range <>) of Character;

      X : My_String := "foo"; --@RANGE_CHECK:FAIL
   begin
      null;
   end Test_Mod_Too_Big;

   procedure Test_Mod_Wrap_Around with Global => null is
      type Small_Int is new Mod_8 range 1 .. Id (6);
      type My_String is array (Small_Int range <>) of Character;

      X : My_String := "foo_bar"; --@RANGE_CHECK:FAIL
   begin
      null;
   end Test_Mod_Wrap_Around;

   procedure Test_Mod_Wrap_Around_2 with Global => null is
      type Small_Int is new Mod_8 range 6 .. Id (7);
      type My_String is array (Small_Int range <>) of Character;

      X : My_String := "foo"; --@RANGE_CHECK:FAIL
   begin
      null;
   end Test_Mod_Wrap_Around_2;
begin
   Test_Mod_Empty_1;
   Test_Mod_Empty_3;
   Test_Mod_Ok_2;
end Test_String_Literals;
