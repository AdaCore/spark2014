with Ada.Unchecked_Conversion;

procedure Record_Padding with SPARK_Mode is
   type Byte is mod 2 ** 8 with Size => 8;
   type Word is mod 2 ** 16 with Size => 16;
   type Inner is array (2 .. 0) of Byte with Size => 0;
   type Outer is array (2 .. 0) of Inner with Size => 8;
   type Rec is record
      Padding : Outer;
      Value   : Byte;
   end record with Size => 16, Alignment => 2;
   for Rec use record
      Padding at 0 range 0 .. 7;
      Value   at 1 range 0 .. 7;
   end record;
   function Convert is new Ada.Unchecked_Conversion (Rec, Word);
   Storage : aliased Word := 16#1234#;
   X : Rec with Import, Address => Storage'Address;
   Y : Word := Convert (X);
begin
   --  The low byte contains padding, whose bits are not modeled
   pragma Assert (Y = 16#1200#); --@ASSERT:FAIL
end Record_Padding;
