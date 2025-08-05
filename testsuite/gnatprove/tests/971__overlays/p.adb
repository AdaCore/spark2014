procedure P with SPARK_Mode is
   type Bit_Array is array (Positive range <>) of Boolean;
   type T1_Bit_Array is new Bit_Array (1 .. 128) with Pack;
   type T2_Bit_Array is new Bit_Array (1 .. 64) with Pack;

   type T1 is record
      F1 : Integer;
      F2 : Natural;
      F3 : Boolean;
      F4 : aliased T2_Bit_Array;
   end record with
     Size => 128;
   for T1 use record
      F1 at 0 range 0 .. 31;
      F2 at 0 range 32 .. 62;
      F3 at 0 range 63 .. 63;
      F4 at 0 range 64 .. 127;
   end record;

   type T2_Unused_Bits is record
      G : Integer;
   end record with
     Size => 64;
   for T2_Unused_Bits use record
      G at 0 range 0 .. 31;
   end record;

   type T2_Invalid_Values is record
      H1 : Positive;
      H2 : Integer;
   end record with
     Size => 64;

   procedure Parse_T1 (X : aliased T1_Bit_Array) is
      Y : aliased constant T1 with
        Import,
        Address => X'Address;

      procedure Parse_T2_Unused_Bits (X : aliased T2_Bit_Array) is
         Z : aliased constant T2_Unused_Bits with
           Import,
           Address => X'Address;
      begin
         --  Here you can access Y's and Z's fields
         null;
      end Parse_T2_Unused_Bits;

      procedure Parse_T2_Invalid_Values (X : aliased T2_Bit_Array) is
         Z : aliased constant T2_Invalid_Values with
           Import,
           Address => X'Address,
           Potentially_Invalid;
      begin
         --  Here you can access Y's and Z's fields

         --  Z.H2 can only have valid values, so it can be used directly
         if Z.H2 = 0 then
            null;
         end if;

         --  Z.H1 might have invalid values, so its validity shall be verified
         if Z.H1'Valid and then Z.H1 = 0 then
            null;
         end if;
      end Parse_T2_Invalid_Values;

   begin
      if Y.F3 then
         Parse_T2_Unused_Bits (Y.F4);
      else
         Parse_T2_Invalid_Values (Y.F4);
      end if;
   end Parse_T1;

begin
   null;
end;
