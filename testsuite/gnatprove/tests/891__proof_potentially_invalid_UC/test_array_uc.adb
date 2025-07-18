with Ada.Unchecked_Conversion;
procedure Test_Array_Uc (C : Integer) with spark_mode is

   type T_1_1000 is new Integer range 1 .. 1000 with Size => Integer'Size;
   type Arr_Bool is array (1 .. 4) of Boolean with Component_Size => 8, Size => Integer'Size;
   type Int_8 is range -2**7 .. 2**7 - 1 with Size => 8, Object_Size => 8;
   subtype Nat_8 is Int_8 range -1 .. 2**7 - 1 with Object_Size => 8;
   type Arr_Nat_8 is array (1 .. 4) of Nat_8 with Component_Size => 8, Size => Integer'Size;

   function F_1_1000_To_Arr_Bool is new Ada.Unchecked_Conversion (T_1_1000, Arr_Bool) with Potentially_Invalid;
   function F_1_1000_To_Arr_Nat_8 is new Ada.Unchecked_Conversion (T_1_1000, Arr_Nat_8) with Potentially_Invalid;
   function F_Arr_Nat_8_To_1_1000 is new Ada.Unchecked_Conversion (Arr_Nat_8, T_1_1000) with Potentially_Invalid;

   procedure Test_1 is
      X_1_1000 : T_1_1000 := 257;
      X_Arr : Arr_Bool := F_1_1000_To_Arr_Bool (X_1_1000); --  @VALIDITY_CHECK:PASS
   begin
      null;
   end Test_1;

   procedure Test_2 is
      X_1_1000 : T_1_1000 := 513;
      X_Arr : Arr_Bool := F_1_1000_To_Arr_Bool (X_1_1000); --  @VALIDITY_CHECK:FAIL
   begin
      null;
   end Test_2;

   procedure Test_3 is
      X_1_1000 : T_1_1000 := 257;
      X_Arr : Arr_Nat_8 := F_1_1000_To_Arr_Nat_8 (X_1_1000); --  @VALIDITY_CHECK:PASS
   begin
      null;
   end Test_3;

   procedure Test_4 is
      X_1_1000 : T_1_1000 := 128;
      X_Arr : Arr_Nat_8 := F_1_1000_To_Arr_Nat_8 (X_1_1000); --  @VALIDITY_CHECK:FAIL
   begin
      null;
   end Test_4;

   procedure Test_5 is
      X_Arr : Arr_Nat_8 := (1, 1, 0, 0);
      X_1_1000 : T_1_1000 := F_Arr_Nat_8_To_1_1000 (X_Arr); --  @VALIDITY_CHECK:PASS
   begin
      null;
   end Test_5;

   procedure Test_6 is
      X_Arr : Arr_Nat_8 := (1, 1, 1, 0);
      X_1_1000 : T_1_1000 := F_Arr_Nat_8_To_1_1000 (X_Arr); --  @VALIDITY_CHECK:FAIL
   begin
      null;
   end Test_6;
begin
   null;
end;
