with Ext; use Ext;
with System;
with System.Storage_Elements; use System.Storage_Elements;

procedure Test with Spark_Mode is

   --  Unsupported address

   X3 : R with Potentially_Invalid, Import, Address => System'To_Address (16#FFFF00A0#);

   procedure P3 (X, Y : R) with Potentially_Invalid => X, Post => True;

   procedure P3 (X, Y : R) is
   begin
      X3 := X;  -- @VALIDITY_CHECK:NONE
      if not X3'Valid_Scalars then
         X3 := Y;
      end if;
      pragma Assert (X3'Valid_Scalars); --  @ASSERT:PASS
   end P3;

   procedure P4 (X, Y : R) with Potentially_Invalid => X, Post => True;

   procedure P4 (X, Y : R) is
   begin
      V := X;  -- @VALIDITY_CHECK:NONE
      V := Y;
      declare
         L : constant R := V with Potentially_Invalid;
      begin
         --  V has asynchronous writers, its value might not be valid
         pragma Assert (L'Valid_Scalars); --  @ASSERT:FAIL
      end;
      declare
         --  V has asynchronous writers, its value might not be valid
         L : constant R := V;  -- @VALIDITY_CHECK:FAIL
      begin
         pragma Assert (L'Valid_Scalars);
      end;
   end P4;

begin
   null;
end;
