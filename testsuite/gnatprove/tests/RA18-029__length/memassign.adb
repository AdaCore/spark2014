with System;

procedure Memassign with SPARK_Mode is

   type size_t is mod 2 ** Standard'Address_Size;

   type IA is mod System.Memory_Size;

   type Byte is mod 2 ** 8;
   for Byte'Size use 8;

   subtype Address is IA;

   type Memory is array (Address) of Byte;

   Mem : Memory;

   procedure memmove
     (Dest : Address; Src : Address; N : size_t)
   with
     Global => (In_Out => Mem),
     Pre    => N > 0 and
               Address'Last - Dest > IA(N) and
               Address'Last - Src > IA(N)
   is
   begin
      Mem (Dest) := Mem (Src);
      Mem (Dest .. Dest + 1) := Mem (Src .. Src + 1);
      Mem (Dest .. Dest + IA(N) - 1) := Mem (Src .. Src + IA(N) - 1);
   end memmove;

begin
   null;
end Memassign;
