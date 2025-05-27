with Ada.Unchecked_Conversion;
with Interfaces; use Interfaces;
procedure Test_Record_UC (C : Integer) with spark_mode is

   type T_1_1000 is new Integer range 1 .. 1000 with Size => Integer'Size;
   type T_m5_50 is new Integer range -5 .. 50 with Object_Size => Integer'Size, Size => Integer'Size;
   type T_1_C is new Integer range 1 .. C with Object_Size => Integer'Size;
   type T_Mod is mod 42 with Object_Size => Integer'Size;
   type T_Bool is new Boolean with Object_Size => Integer'Size;

   type R_m5_50 is record
      F : T_m5_50;
   end record with Size => Integer'Size;
   for R_m5_50 use
      record
         F at 0 range 0 .. 31;
      end record;
   type R_1_C is record
      F : T_1_C;
   end record with Size => Integer'Size;
   for R_1_C use
      record
         F at 0 range 0 .. 31;
      end record;
   type R_Mod is record
      F : T_Mod;
   end record with Size => Integer'Size;
   for R_Mod use
      record
         F at 0 range 0 .. 31;
      end record;
   type R_Bool is record
      F : T_Bool;
   end record with Size => Integer'Size;
   for R_Bool use
      record
         F at 0 range 0 .. 31;
      end record;
   type R_Bool_2 is record
      F, G : Boolean;
   end record with Size => 16;
   for R_Bool_2 use
      record
         F at 0 range 0 .. 7;
         G at 0 range 8 .. 15;
      end record;
   type R_Bool_4 is record
      F : Boolean;
      G : R_Bool_2;
      H : Boolean;
   end record with Size => Integer'Size;
   for R_Bool_4 use
      record
         F at 0 range 0 .. 7;
         G at 0 range 8 .. 23;
         H at 0 range 24 .. 31;
      end record;

   function F_m5_50_To_1_1000 is new Ada.Unchecked_Conversion (R_m5_50, T_1_1000) with Potentially_Invalid;
   function F_1_1000_To_m5_50 is new Ada.Unchecked_Conversion (T_1_1000, R_m5_50) with Potentially_Invalid;
   function F_1_1000_To_1_C is new Ada.Unchecked_Conversion (T_1_1000, R_1_C) with Potentially_Invalid;
   function F_1_1000_To_Mod is new Ada.Unchecked_Conversion (T_1_1000, R_Mod) with Potentially_Invalid;
   function F_1_1000_To_Bool is new Ada.Unchecked_Conversion (T_1_1000, R_Bool) with Potentially_Invalid;
   function F_Uns_32_To_Bool_4 is new Ada.Unchecked_Conversion (Unsigned_32, R_Bool_4) with Potentially_Invalid;

   procedure Test_1 is
      X_m5_50 : R_m5_50 := (F => 44);
      X_1_1000 : T_1_1000 := F_m5_50_To_1_1000 (X_m5_50); --  @VALIDITY_CHECK:PASS
   begin
      null;
   end Test_1;

   procedure Test_2 is
      X_m5_50 : R_m5_50 := (F => -2);
      X_1_1000 : T_1_1000 := F_m5_50_To_1_1000 (X_m5_50); --  @VALIDITY_CHECK:FAIL
   begin
      null;
   end Test_2;

   procedure Test_3 is
      X_1_1000 : T_1_1000 := 44;
      X_m5_50 : R_m5_50 := F_1_1000_To_m5_50 (X_1_1000); --  @VALIDITY_CHECK:PASS
   begin
      null;
   end Test_3;

   procedure Test_4 is
      X_1_1000 : T_1_1000 := 100;
      X_m5_50 : R_m5_50 := F_1_1000_To_m5_50 (X_1_1000); --  @VALIDITY_CHECK:FAIL
   begin
      null;
   end Test_4;

   procedure Test_5 is
      X_1_1000 : T_1_1000 := 4;
      X_Mod : R_Mod := F_1_1000_To_Mod (X_1_1000); --  @VALIDITY_CHECK:PASS
   begin
      null;
   end Test_5;

   procedure Test_6 is
      X_1_1000 : T_1_1000 := 100;
      X_Mod : R_Mod := F_1_1000_To_Mod (X_1_1000); --  @VALIDITY_CHECK:FAIL
   begin
      null;
   end Test_6;

   procedure Test_7 is
      X_1_1000 : T_1_1000 := 1;
      X_Bool : R_Bool := F_1_1000_To_Bool (X_1_1000); --  @VALIDITY_CHECK:PASS
   begin
      null;
   end Test_7;

   procedure Test_8 is
      X_1_1000 : T_1_1000 := 100;
      X_Bool : R_Bool := F_1_1000_To_Bool (X_1_1000); --  @VALIDITY_CHECK:FAIL
   begin
      null;
   end Test_8;

   procedure Test_9 is
      X_32 : Unsigned_32 := 257;
      X_Bool : R_Bool_4 := F_Uns_32_To_Bool_4 (X_32); --  @VALIDITY_CHECK:PASS
   begin
      pragma Assert (X_Bool.F);
      pragma Assert (not X_Bool.H);
   end Test_9;

   procedure Test_10 is
      X_32 : Unsigned_32 := 512;
      X_Bool : R_Bool_4 := F_Uns_32_To_Bool_4 (X_32); --  @VALIDITY_CHECK:FAIL
   begin
      null;
   end Test_10;

   procedure Test_11 with Pre => C >= 44;

   procedure Test_11 is
      X_1_1000 : T_1_1000 := 44;
      X_1_C : R_1_C := F_1_1000_To_1_C (X_1_1000); --  @VALIDITY_CHECK:PASS
   begin
      null;
   end Test_11;

   procedure Test_12 is
      X_1_1000 : T_1_1000 := 44;
      X_1_C : R_1_C := F_1_1000_To_1_C (X_1_1000); --  @VALIDITY_CHECK:FAIL
   begin
      null;
   end Test_12;
begin
   null;
end;
