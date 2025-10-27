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
      with Import, Address => X (1 .. 16)'Address;
   begin
      Parse_T1 (Y);
   end P1;

begin
   null;
end Main;
