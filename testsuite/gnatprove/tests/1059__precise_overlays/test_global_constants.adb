procedure Test_Global_Constants with SPARK_Mode is

   type Int_8 is range - 128 .. 127;
   type Mod_8 is mod 256;
   type Int_Arr is array (1 .. 4) of aliased Int_8;
   type Mod_Arr is array (1 .. 4) of aliased Mod_8;
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

   procedure Test_Int_OK is
      X : constant Int_8 := 0;
      Y : constant Mod_8 with Import, Address => X'Address;
      procedure Test is
      begin
         pragma Assert (Y = 0);
      end;
   begin
      null;
   end;

   procedure Test_Int_KO is
      X : constant Int_8 := -1;
      Y : constant Mod_8 with Import, Address => X'Address;
      procedure Test is
      begin
         pragma Assert (Y = 0); -- @ASSERT:FAIL
      end;
   begin
      null;
   end;

   procedure Test_Array_OK is
      X : constant Int_Arr := (others => 0);
      Y : constant Mod_Arr with Import, Address => X'Address;
      procedure Test is
      begin
         pragma Assert (Y (1) = 0);
      end;
   begin
      null;
   end;

   procedure Test_Array_KO is
      X : constant Int_Arr := (others => -1);
      Y : constant Mod_Arr with Import, Address => X'Address;
      procedure Test is
      begin
         pragma Assert (Y (1) = 0); -- @ASSERT:FAIL
      end;
   begin
      null;
   end;

   procedure Test_Record_OK is
      I : Int_8 := 0;
      X : constant Int_Rec := (others => I);
      Y : constant Mod_Rec with Import, Address => X'Address;
      procedure Test with Pre => X.F = 0 is
      begin
         pragma Assert (Y.F = 0);
      end;
   begin
      null;
   end;

   procedure Test_Record_KO is
      I : Int_8 := -1;
      X : constant Int_Rec := (others => I);
      Y : constant Mod_Rec with Import, Address => X'Address;
      procedure Test with Pre => X.F = -1 is
      begin
         pragma Assert (Y.F = 0); -- @ASSERT:FAIL
      end;
   begin
      null;
   end;
begin
   null;
end;
