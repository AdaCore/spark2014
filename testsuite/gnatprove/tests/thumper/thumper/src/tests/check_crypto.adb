---------------------------------------------------------------------------
-- FILE    : check_crypto.adb
-- SUBJECT : Package containing tests of the cryptographic services.
-- AUTHOR  : (C) Copyright 2015 by Peter C. Chapin
--
-- Please send comments or bug reports to
--
--      Peter C. Chapin <PChapin@vtc.vsc.edu>
---------------------------------------------------------------------------
with AUnit.Assertions;       use AUnit.Assertions;
with Cryptographic_Services; use Cryptographic_Services;
with Hermes;

package body Check_Crypto is

   procedure Test_Hashing(T : in out AUnit.Test_Cases.Test_Case'Class) is
      pragma Unreferenced(T);

      use type Hermes.Octet_Array;

      Input_1 : constant Hermes.Octet_Array(1 .. 5) :=
        (72, 101, 108, 108, 111);  -- "Hello"
      Expected_1 : constant Hermes.Octet_Array(1 .. 32) :=
        (16#18#, 16#5f#, 16#8d#, 16#b3#, 16#22#, 16#71#, 16#fe#, 16#25#,
         16#f5#, 16#61#, 16#a6#, 16#fc#, 16#93#, 16#8b#, 16#2e#, 16#26#,
         16#43#, 16#06#, 16#ec#, 16#30#, 16#4e#, 16#da#, 16#51#, 16#80#,
         16#07#, 16#d1#, 16#76#, 16#48#, 16#26#, 16#38#, 16#19#, 16#69#);

      Input_2 : constant Hermes.Octet_Array(1 .. 13) :=
        (72, 101, 108, 108, 111, 44, 32, 87, 111, 114, 108, 100, 33); -- "Hello, World!"
      Expected_2 : constant Hermes.Octet_Array(1 .. 32) :=
        (16#df#, 16#fd#, 16#60#, 16#21#, 16#bb#, 16#2b#, 16#d5#, 16#b0#,
         16#af#, 16#67#, 16#62#, 16#90#, 16#80#, 16#9e#, 16#c3#, 16#a5#,
         16#31#, 16#91#, 16#dd#, 16#81#, 16#c7#, 16#f7#, 16#0a#, 16#4b#,
         16#28#, 16#68#, 16#8a#, 16#36#, 16#21#, 16#82#, 16#98#, 16#6f#);

      -- TODO: Add more test cases to explore "interesting" boundary values.
   begin
      Initialize_Hash;
      Update_Hash(Input_1);
      Assert(Finalize_Hash = Expected_1, "SHA256 hash of Input_1 does not check");

      Initialize_Hash;
      Update_Hash(Input_2( 1 .. 10));
      Update_Hash(Input_2(11 .. 13));
      Assert(Finalize_Hash = Expected_2, "SHA256 hash of Input_2 does not check");
   end Test_Hashing;


   procedure Register_Tests(T : in out Crypto_Test) is
   begin
      AUnit.Test_Cases.Registration.Register_Routine(T, Test_Hashing'Access, "Hashing");
   end Register_Tests;


   function Name(T : Crypto_Test) return AUnit.Message_String is
      pragma Unreferenced(T);
   begin
      return AUnit.Format("Crypto");
   end Name;

end Check_Crypto;
