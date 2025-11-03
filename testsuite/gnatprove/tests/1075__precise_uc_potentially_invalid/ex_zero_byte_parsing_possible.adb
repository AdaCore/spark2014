with Ada.Unchecked_Conversion;
procedure Ex_Zero_Byte_Parsing_Possible with SPARK_Mode is
   type Bit_Array is array (Positive range <>) of Boolean;
   type T2_Bit_Array is new Bit_Array (1 .. 64) with Pack;

   type T2_Kind_1 is record
      G1 : Integer;
      G2 : Natural;  --  Might have invalid values
   end record
   with Size => 64;
   for T2_Kind_1 use
     record
       G1 at 0 range 0 .. 31;
       G2 at 0 range 32 .. 63;
     end record;

   package Model with Ghost is
      function T2_From_Bytes is new Ada.Unchecked_Conversion
        (T2_Bit_Array, T2_Kind_1)
        with Potentially_Invalid;

      function Is_Valid (X : T2_Bit_Array) return Boolean is
        (T2_From_Bytes (X)'Valid_Scalars);
   end Model;

   procedure Parse_T2_Kind_1 (X : aliased T2_Bit_Array) with
     Pre => Model.Is_Valid (X);

   procedure Parse_T2_Kind_1 (X : aliased T2_Bit_Array) is
      Z : aliased constant T2_Kind_1 with
        Import,
        Address => X'Address,
        Potentially_Invalid;
   begin
      pragma Assert (Z.G2'Valid); --  This is not provable yet
   end Parse_T2_Kind_1;

begin
   null;
end;
