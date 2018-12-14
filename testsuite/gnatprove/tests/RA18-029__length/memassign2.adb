procedure Memassign2 with SPARK_Mode is

   type Byte is mod 2 ** 8;

   type Address is mod 2 ** 64;

   type Memory is array (Address) of Byte;

   Mem : Memory;

   procedure memmove
     (Dest : Address; Src : Address)
   with
     Global => (In_Out => Mem),
     Pre    => Address'Last - Dest > 0 and
               Address'Last - Src > 0
   is
   begin
      pragma Assert (Dest <= Dest + 1);
      pragma Assert (Src <= Src + 1);
      Mem (Dest .. Dest + 1) := Mem (Src .. Src + 1);
   end memmove;

begin
   null;
end Memassign2;
