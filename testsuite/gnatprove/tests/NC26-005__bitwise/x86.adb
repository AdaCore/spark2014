package body X86
with SPARK_Mode
is

   function ReadMem8(addr : in Unsigned64) return Unsigned8
   is
   begin
      return Memory(addr);
   end ReadMem8;


   procedure WriteMem8(addr : in Unsigned64; Val : in Unsigned8)
   is
   begin
      Memory(addr) := Val;
   end WriteMem8;


   function ReadMem16(addr: in Unsigned64) return Unsigned16
   is
   begin
      return (Unsigned16(ReadMem8(addr)) or
                Shift_Left(Unsigned16(ReadMem8(addr+1)),8));
   end ReadMem16;

   procedure WriteMem16(addr : in Unsigned64; Val : in Unsigned16)
   is
   begin
      WriteMem8(addr, Unsigned8(Val and 16#00FF#));
      WriteMem8(addr+1,Unsigned8(Shift_Right(Val,8) and 16#00FF#));
   end WriteMem16;

   procedure WriteMem16_v2(addr : in Unsigned64; Val : in Unsigned16)
   is
   begin
      WriteMem8(addr, Unsigned8(Val and 16#00FF#));
      WriteMem8(addr+1,Unsigned8(Shift_Right(Val,8) and 16#00FF#));
   end WriteMem16_v2;



end X86;
