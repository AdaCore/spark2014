with Ada.Unchecked_Conversion;
procedure Test_Scalar_UC (C : Integer) with spark_mode is

   type T_1_100 is new Integer range 1 .. 100 with Size => Integer'Size;
   type T_5_lst is new Integer range 5 .. Integer'Last with Size => Integer'Size;
   type T_1_C is new Integer range 1 .. C with Size => Integer'Size;
   type T_Mod is mod 42 with Size => Integer'Size;
   type T_Bool is new Boolean with Size => Integer'Size;
   type T_Empty is new Integer range 1 .. 0 with Size => Integer'Size;

   function F_1_100_To_5_lst is new Ada.Unchecked_Conversion (T_1_100, T_5_lst) with Potentially_Invalid;
   function F_1_100_To_1_C is new Ada.Unchecked_Conversion (T_1_100, T_1_C) with Potentially_Invalid;
   function F_1_100_To_Mod is new Ada.Unchecked_Conversion (T_1_100, T_Mod) with Potentially_Invalid;
   function F_1_100_To_T_Bool is new Ada.Unchecked_Conversion (T_1_100, T_Bool) with Potentially_Invalid;
   function F_1_100_To_Empty is new Ada.Unchecked_Conversion (T_1_100, T_Empty) with Potentially_Invalid;

   procedure Test_1 is
      X_1_100 : T_1_100 := 44;
      X_5_Lst : T_5_Lst := F_1_100_To_5_Lst (X_1_100); --  @VALIDITY_CHECK:PASS
   begin
      null;
   end Test_1;

   procedure Test_2 is
      X_1_100 : T_1_100 := 4;
      X_5_Lst : T_5_Lst := F_1_100_To_5_Lst (X_1_100); --  @VALIDITY_CHECK:FAIL
   begin
      null;
   end Test_2;

   procedure Test_3 with Pre => C > 4;

   procedure Test_3 is
      X_1_100 : T_1_100 := 4;
      X_1_C : T_1_C := F_1_100_To_1_C (X_1_100); --  @VALIDITY_CHECK:PASS
   begin
      null;
   end Test_3;

   procedure Test_4 is
      X_1_100 : T_1_100 := 4;
      X_1_C : T_1_C := F_1_100_To_1_C (X_1_100); --  @VALIDITY_CHECK:FAIL
   begin
      null;
   end Test_4;

   procedure Test_5 is
      X_1_100 : T_1_100 := 1;
      X_Bool : T_Bool := F_1_100_To_T_Bool (X_1_100); --  @VALIDITY_CHECK:PASS
   begin
      null;
   end Test_5;

   procedure Test_6 is
      X_1_100 : T_1_100 := 4;
      X_Bool : T_Bool := F_1_100_To_T_Bool (X_1_100); --  @VALIDITY_CHECK:FAIL
   begin
      null;
   end Test_6;

   procedure Test_7 is
      X_1_100 : T_1_100 := 4;
      X_Mod : T_Mod := F_1_100_To_Mod (X_1_100); --  @VALIDITY_CHECK:PASS
   begin
      null;
   end Test_7;

   procedure Test_8 is
      X_1_100 : T_1_100 := 100;
      X_Mod : T_Mod := F_1_100_To_Mod (X_1_100); --  @VALIDITY_CHECK:FAIL
   begin
      null;
   end Test_8;

   procedure Test_9 is
      X_1_100 : T_1_100 := 100;
      X_5_Empty : T_Empty'Base := F_1_100_To_Empty (X_1_100); --  @VALIDITY_CHECK:FAIL
   begin
      null;
   end Test_9;
begin
   null;
end;
