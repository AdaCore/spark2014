procedure Main with SPARK_Mode is
   type Int_8 is mod 256 with Size => 8;
   type Byte_Array is array (Positive range <>) of aliased Int_8
   with Component_Size => 8, Pack;
   subtype T1_Byte_Array is Byte_Array (1 .. 16);

   procedure Parse_T1 (X : aliased T1_Byte_Array) is
      C : not null access constant T1_Byte_Array := X'Access;
   begin
      null;
   end Parse_T1;

   procedure P1 (X : aliased Byte_Array)
   with Pre => X'First = 1 and then X'Last >= 16;

   procedure P1 (X : aliased Byte_Array) is
      Y : aliased constant T1_Byte_Array
      with Import, Address => X (1 .. 16)'Address, Alignment => 8;
   begin
      Parse_T1 (Y);
   end P1;

   procedure P2 (X : aliased Byte_Array; D : Positive)
   with
     Pre => X'First <= D and then X'Last >= X'First and then D <= X'Last - 15;

   procedure P2 (X : aliased Byte_Array; D : Positive) is
      Y : aliased constant T1_Byte_Array
      with Import, Address => X (D .. D + 15)'Address, Alignment => 8;
   begin
      Parse_T1 (Y);
   end P2;

   procedure P3 (X : aliased Byte_Array)
   with Pre => X'First = 1 and then X'Last >= 16;

   procedure P3 (X : aliased Byte_Array) is
      Y : aliased constant T1_Byte_Array
      with Import, Address => X (1 .. 15)'Address, Alignment => 8; --  @UNCHECKED_CONVERSION_SIZE:FAIL
   begin
      Parse_T1 (Y);
   end P3;

   procedure P4 (X : aliased Byte_Array; D : Positive)
   with
     Pre => X'First <= D and then X'Last >= X'First and then D <= X'Last - 16;

   procedure P4 (X : aliased Byte_Array; D : Positive) is
      Y : aliased constant T1_Byte_Array
      with
        Import,
        Address   => X (D .. D + 16)'Address, --  @UNCHECKED_CONVERSION_SIZE:FAIL
        Alignment => 8;
   begin
      Parse_T1 (Y);
   end P4;

   type Byte_Array_Gap is array (Positive range <>) of Int_8
   with Component_Size => 11;
   subtype T1_Byte_Array_Gap is Byte_Array_Gap (1 .. 2);

   function Id (X : Integer) return Integer is (X);

   procedure P5 (X : aliased Byte_Array_Gap);

   procedure P5 (X : aliased Byte_Array_Gap) is
      Y : aliased constant T1_Byte_Array_Gap --  The alias is not precisely supported, there might be gaps
      with
        Import,
        Address   => X (Id (1) .. 2)'Address,
        Alignment => 8;
   begin
      null;
   end P5;

begin
   null;
end Main;
