procedure Test_Dynamic_String_Literals with SPARK_Mode is
   function Id (X : Integer) return Integer with Post => Id'Result = X;
   function Id (X : Integer) return Integer is
   begin
      if X = 1 then
         return 1;
      else
         return X;
      end if;
   end Id;

   procedure Test_Signed_Bad_Fst with Global => null is
      type My_Int is new Integer;
      function Id (X : My_Int) return My_Int is (X);
      subtype Small_Int is My_Int range 12 .. 14;
      type My_String is array (Small_Int range <>) of Character;

      X : My_String (Id (11) .. Id (13)) := "foo"; --@RANGE_CHECK:FAIL
   begin
      null;
   end Test_Signed_Bad_Fst;

   type Mod_8 is mod 8;
   function Id (X : Mod_8) return Mod_8 with Post => Id'Result = X;
   function Id (X : Mod_8) return Mod_8 is (X);

   procedure Test_Mod_Empty_2 with Global => null is
      type Small_Int is new Mod_8 range Id (0) .. 7;
      type My_String is array (Small_Int range <>) of Character;

      X : My_String := ""; --@RANGE_CHECK:FAIL
   begin
      null;
   end Test_Mod_Empty_2;

   procedure Test_Mod_Empty_4 with Global => null is
      type Small_Int is new Mod_8 range Id (1) .. 7;
      type My_String is array (Small_Int range <>) of Character;

      X : My_String := ""; --@RANGE_CHECK:PASS
   begin
      null;
   end Test_Mod_Empty_4;

   procedure Test_Mod_Ok_1 with Global => null is
      type Small_Int is new Mod_8 range Id (0) .. 7;
      type My_String is array (Small_Int range <>) of Character;

      X : My_String := "aaa"; --@RANGE_CHECK:PASS
   begin
      pragma Assert (X'First = 0); --@ASSERT:PASS
   end Test_Mod_Ok_1;

   procedure Test_Mod_Ok_2 with Global => null is
      type Mod_256 is mod 256;
      function Id (X : Mod_256) return Mod_256 is (X);
      type Small_Int is new Mod_256 range Id (0) .. 255;
      type My_String is array (Small_Int range <>) of Character;

      X : My_String := "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"; --@RANGE_CHECK:PASS
   begin
      pragma Assert (X'Length = 256);
   end Test_Mod_Ok_2;

   procedure Test_Mod_Ok_3 with Global => null is
      type Small_Int is new Mod_8 range Id (0) .. Id(2);
      type My_String is array (Small_Int range <>) of Character;

      X : My_String := "foo"; --@RANGE_CHECK:PASS
   begin
      null;
   end Test_Mod_Ok_3;

   procedure Test_Mod_Too_Big with Global => null is
      type Small_Int is new Mod_8 range Id (0) .. Id(1);
      type My_String is array (Small_Int range <>) of Character;

      X : My_String := "foo"; --@RANGE_CHECK:FAIL
   begin
      null;
   end Test_Mod_Too_Big;

   procedure Test_Mod_Wrap_Around with Global => null is
      type Small_Int is new Mod_8 range Id (1) .. 7;
      type My_String is array (Small_Int range <>) of Character;

      X : My_String := "foo_bar_"; --@RANGE_CHECK:FAIL
   begin
      null;
   end Test_Mod_Wrap_Around;

   procedure Test_Mod_Wrap_Around_2 with Global => null is
      type Small_Int is new Mod_8 range Id (6) .. 7;
      type My_String is array (Small_Int range <>) of Character;

      X : My_String := "foo"; --@RANGE_CHECK:FAIL
   begin
      null;
   end Test_Mod_Wrap_Around_2;
begin
   Test_Mod_Empty_4;
   Test_Mod_Ok_1;
   Test_Mod_Ok_3;
end Test_Dynamic_String_Literals;
