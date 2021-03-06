procedure Use_Bytes2 is

   type Rec is record
      A, B, C : Integer;
   end record with Size => 96, Alignment => 4, Object_Size => 96;

   R : aliased Rec := (0, 1, 41);

   type U32 is mod 2**32;
   subtype Payload is Rec;

   type Base is array (Integer range <>) of U32
     with Pack, Component_Size => U32'Size, Alignment => 4;

   function Extract (Data : aliased Payload) return U32 is
      subtype Arr is Base (1 .. Rec'Size / U32'Size);
      Data_Arr : constant Arr
        with Address => Data'Address, Import, Alignment => 4;
      Res : U32 := 0;
   begin
      for Value of Data_Arr loop
         Res := Res + Value;
      end loop;
      return Res;
   end Extract;

begin
   pragma Assert (Extract (R) = 42);
end Use_Bytes2;
