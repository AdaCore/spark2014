package body X86
with SPARK_Mode
is

   function AL return Unsigned8 is
   begin
      return Unsigned8(RAX and 16#00000000000000FF#);
   end AL;

   procedure Write_AL(Val : in Unsigned8) is
   begin
      RAX := (RAX and 16#FFFFFFFFFFFFFF00#) or Unsigned64(Val);
   end Write_AL;

   function AH return Unsigned8 is
   begin
      return Unsigned8'Mod((RAX and 16#000000000000FF00#) / 256);
   end AH;

   procedure Write_AH(Val : in Unsigned8) is
   begin
      RAX := ((RAX and 16#000000000000FF00#) or Unsigned64(Unsigned16(Val) * 256));
   end Write_AH;

   function AX return Unsigned16 is
   begin
      return Unsigned16(RAX and 16#000000000000FFFF#);
   end AX;

   procedure Write_AX(Val : in Unsigned16) is
   begin
      RAX := (RAX and 16#FFFFFFFFFFFF0000#) or Unsigned64(Val);
   end Write_AX;

   function EAX return Unsigned32 is
   begin
      return Unsigned32(RAX and 16#00000000FFFFFFFF#);
   end EAX;

   procedure Write_EAX(Val : in Unsigned32) is
   begin
      RAX := (RAX and 16#FFFFFFFF00000000#) or Unsigned64(Val);
   end Write_EAX;

   -----------------------------------------------------------------------
   --			            Main     	        		--
   -----------------------------------------------------------------------

   procedure Main is
   begin
      Write_AL(1);
   end Main;

   -----------------------------------------------------------------------
   --			      Read/Write Memory 			--
   -----------------------------------------------------------------------

   -- Saves a 64-bit Value to Memory
   -- Note that this will wrap if addr > 2**64-7
   procedure WriteMem64(addr : in Unsigned64; Val : in Unsigned64)
   is
   begin
      -- SPARK should be able to prove the following assert, but it cannot (yet)
--      pragma Assert ((Val and 16#FFFFFFFFFFFFFF00#) < 256);
      Memory(addr) := Unsigned8'Mod(Val and 16#FF#);
      Memory(addr + 1) := Unsigned8'Mod(Shift_Right(Val, 8) and 16#FF#);
      Memory(addr + 2) := Unsigned8'Mod(Shift_Right(Val, 16) and 16#FF#);
      Memory(addr + 3) := Unsigned8'Mod(Shift_Right(Val, 24) and 16#FF#);
      Memory(addr + 4) := Unsigned8'Mod(Shift_Right(Val, 32) and 16#FF#);
      Memory(addr + 5) := Unsigned8'Mod(Shift_Right(Val, 40) and 16#FF#);
      Memory(addr + 6) := Unsigned8'Mod(Shift_Right(Val, 48) and 16#FF#);
      Memory(addr + 7) := Unsigned8'Mod(Shift_Right(Val, 56) and 16#FF#);
   end WriteMem64;

end X86;
