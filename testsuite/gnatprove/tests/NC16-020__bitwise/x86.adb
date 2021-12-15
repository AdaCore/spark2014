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

end X86;
