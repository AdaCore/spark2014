package body X86
with SPARK_Mode
is
   function DL return Unsigned_8 is
   begin
      return Unsigned_8(RDX and 16#00000000000000FF#);
   end DL;

   procedure Write_DL(Val : in Unsigned_8) is
   begin
      RDX := (RDX and 16#FFFFFFFFFFFFFF00#) or Unsigned_64(Val);
   end Write_DL;

   procedure setb_DL
   is
   begin
      if (CarryFlag) then
         Write_DL(1);
      else
         Write_DL(0);
      end if;
   end setb_DL;
end X86;

