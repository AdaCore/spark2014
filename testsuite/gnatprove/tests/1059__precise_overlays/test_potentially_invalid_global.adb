procedure Test_potentially_Invalid_global with SPARK_Mode is

   type Nat_8 is range 0 .. 127 with Size => 8;
   type Mod_8 is mod 256;
   type Int_Arr is array (1 .. 4) of aliased Nat_8;
   type Mod_Arr is array (1 .. 4) of aliased Mod_8;
   type Int_Rec is record
      F, G : Nat_8;
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
      X : constant Mod_8 := 0;
      Y : constant Nat_8 with Import, Address => X'Address, Potentially_Invalid;
      procedure Test is
      begin
         pragma Assert (Y = 0);
      end;
   begin
      null;
   end;

   procedure Test_Int_Invalid is
      X : constant Mod_8 := Mod_8'Last;
      Y : constant Nat_8 with Import, Address => X'Address, Potentially_Invalid;
      procedure Test is
      begin
         pragma Assert (Y'Valid); -- @ASSERT:FAIL
      end;
   begin
      null;
   end;

   procedure Test_Int_KO is
      X : constant Mod_8 := 1;
      Y : constant Nat_8 with Import, Address => X'Address, Potentially_Invalid;
      procedure Test is
      begin
         pragma Assert (Y = 0); -- @ASSERT:FAIL
      end;
   begin
      null;
   end;

   procedure Test_Array_OK is
      X : constant Mod_Arr := (others => 0);
      Y : constant Int_Arr with Import, Address => X'Address, Potentially_Invalid;
      procedure Test is
      begin
         pragma Assert (Y (1) = 0);
      end;
   begin
      null;
   end;

   procedure Test_Array_Invalid is
      X : constant Mod_Arr := (others => Mod_8'Last);
      Y : constant Int_Arr with Import, Address => X'Address, Potentially_Invalid;
      procedure Test is
      begin
         pragma Assert (Y'Valid_Scalars); -- @ASSERT:FAIL
      end;
   begin
      null;
   end;

   procedure Test_Array_KO is
      X : constant Mod_Arr := (others => 1);
      Y : constant Int_Arr with Import, Address => X'Address, Potentially_Invalid;
      procedure Test is
      begin
         pragma Assert (Y (1) = 0); -- @ASSERT:FAIL
      end;
   begin
      null;
   end;

   procedure Test_Record_OK is
      I : Mod_8 := 0;
      X : constant Mod_Rec := (others => I);
      Y : constant Int_Rec with Import, Address => X'Address, Potentially_Invalid;
      procedure Test with Pre => X.F = 0 is
      begin
         pragma Assert (Y.F = 0);
      end;
   begin
      null;
   end;

   procedure Test_Record_Invalid is
      I : Mod_8 := Mod_8'Last;
      X : constant Mod_Rec := (others => I);
      Y : constant Int_Rec with Import, Address => X'Address, Potentially_Invalid;
      procedure Test with Pre => X.F = Mod_8'Last is
      begin
         pragma Assert (Y'Valid_Scalars); -- @ASSERT:FAIL
      end;
   begin
      null;
   end;

   procedure Test_Record_KO is
      I : Mod_8 := 1;
      X : constant Mod_Rec := (others => I);
      Y : constant Int_Rec with Import, Address => X'Address, Potentially_Invalid;
      procedure Test with Pre => X.F = 1 is
      begin
         pragma Assert (Y.F = 0); -- @ASSERT:FAIL
      end;
   begin
      null;
   end;
begin
   null;
end;
