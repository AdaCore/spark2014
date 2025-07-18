with Ext; use Ext;
with System;
with System.Storage_Elements; use System.Storage_Elements;

procedure Test with Spark_Mode is

   --  Overlays, objects with an address clause, and volatile objects cannot be
   --  locally invalid.

   --  Overlays

   X1 : R := (F => 13);
   Y1 : Integer with Import, Address => X1'Address;

   X2 : Integer := 13;
   Y2 : R with Import, Address => X2'Address;

   --  Unsupported address

   X3 : R with Import, Address => System'To_Address (16#FFFF00A0#);

   procedure P1 (X, Y : R) with Potentially_Invalid => X;

   procedure P1 (X, Y : R) is
   begin
      X1 := X;  -- @VALIDITY_CHECK:FAIL
      X1 := Y;
   end P1;

   procedure P2 (X, Y : R) with Potentially_Invalid => X;

   procedure P2 (X, Y : R) is
   begin
      Y2 := X;  -- @VALIDITY_CHECK:FAIL
      Y2 := Y;
   end P2;

   procedure P3 (X, Y : R) with Potentially_Invalid => X;

   procedure P3 (X, Y : R) is
   begin
      X3 := X;  -- @VALIDITY_CHECK:FAIL
      X3 := Y;
   end P3;

   procedure P4 (X, Y : R) with Potentially_Invalid => X;

   procedure P4 (X, Y : R) is
   begin
      V := X;  -- @VALIDITY_CHECK:FAIL
      V := Y;
   end P4;

begin
   null;
end;
