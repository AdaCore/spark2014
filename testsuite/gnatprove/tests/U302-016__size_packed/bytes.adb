package body Bytes is

   type Base is array (Integer range <>) of U32
     with Pack, Component_Size => U32'Size, Alignment => 4;

   function Extract (Data : aliased Payload) return U32 is
      subtype Arr is Base (0 .. (Payload'Size / U32'Size) - 1);
      Data_Arr : constant Arr
        with Address => Data'Address, Import, Alignment => 4;
      Res : U32 := 0;
   begin
      for Value of Data_Arr loop
         Res := Res + Value;
      end loop;
      return Res;
   end Extract;

   procedure Extract_Proc (Data : aliased out Payload) is
      subtype Arr is Base (0 .. (Payload'Size / U32'Size) - 1);
      Data_Arr : Arr
        with Address => Data'Address, Import, Alignment => 4;
   begin
      for Value of Data_Arr loop
         Value := 1;
      end loop;
   end Extract_Proc;

end Bytes;
