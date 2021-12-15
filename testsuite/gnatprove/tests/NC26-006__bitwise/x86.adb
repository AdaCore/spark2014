package body X86
with SPARK_Mode
is

   function ReadMem8(addr : in Unsigned64) return Unsigned8
   is
   begin
      return Memory(addr);
   end ReadMem8;


   function ReadMem16(addr: in Unsigned64) return Unsigned16
   is
   begin
      return (Unsigned16(ReadMem8(addr)) or
                Shift_Left(Unsigned16(ReadMem8(addr+1)),8));
      --	(Unsigned16(ReadMem8(addr + 1)) * (256));
   end ReadMem16;

   function ReadMem32(addr: in Unsigned64) return Unsigned32
   is
   begin
      return (Unsigned32(ReadMem8(addr)) or
                Shift_Left(Unsigned32(ReadMem8(addr+1)),8) or
                Shift_Left(Unsigned32(ReadMem8(addr+2)),16) or
                Shift_Left(Unsigned32(ReadMem8(addr+3)),24));
   end ReadMem32;


   function ReadMem32_v2(addr: in Unsigned64) return Unsigned32
   is
   begin
      return (Unsigned32(ReadMem16(addr)) or
                Shift_Left(Unsigned32(ReadMem16(addr+2)),16));
   end ReadMem32_v2;


end X86;
