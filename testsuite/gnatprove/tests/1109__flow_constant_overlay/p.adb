procedure P with SPARK_Mode is

   type Int_8 is range - 128 .. 127;
   type Mod_8 is mod 256;
   type Int_Rec is record
      F, G : Int_8;
   end record
     with Size => 16;
   for Int_Rec use record
      F at 0 range  0 .. 7;
      G at 0 range  8 .. 15;
   end record;

   type Mod_Rec is record
      F, G : Mod_8;
   end record
     with Size => 16;
   for Mod_Rec use record
      F at 0 range  0 .. 7;
      G at 0 range  8 .. 15;
   end record;

   procedure Test_Record_KO is
      X : constant Int_Rec := (others => -1);
      Y : constant Mod_Rec with Import, Address => X'Address;
      procedure Test is
      begin
         pragma Assert (Y.F = 0); -- @ASSERT:FAIL
      end;
   begin
      null;
   end;
begin
   null;
end;
