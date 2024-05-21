with System; use System;
with System.Storage_Elements; use System.Storage_Elements;

procedure Main with SPARK_Mode is

   type Byte is mod 2**8 with Alignment => 1;
   type Aligned_Integer is mod 2**32 with Alignment => 4;

   procedure Test_Byte (X : Address) with Global => null;
   procedure Test_Integer_Bad (X : Address) with Global => null;
   procedure Test_Integer_Good (X : Address)
     with Global => null, Pre => To_Integer (X) mod 4 = 0;
   procedure Test_Alignment_Transfer with Global => null;
   function Identity (X : Address) return Address
     with Global => null, Post => Identity'Result = X;

   function Identity (X : Address) return Address is
   begin
      return X;
   end Identity;

   procedure Test_Byte (X : Address) is
      Y : Byte with Import, Address => X;
   begin
      null;
   end Test_Byte;

   procedure Test_Integer_Bad (X : Address) is
      Y : Integer with Import, Address => X;
   begin
      null;
   end Test_Integer_Bad;

   procedure Test_Integer_Good (X : Address) is
      Y : Integer with Import, Address => To_Address (To_Integer (X) + 4);
   begin
      null;
   end Test_Integer_Good;

   procedure Test_Alignment_Transfer is
      X : aliased Integer;
      Y : Integer with Import, Address => Identity (X'Address);
   begin
      null;
   end Test_Alignment_Transfer;

begin
   null;
end Main;
