package body X86
with SPARK_Mode
is

   function AL return Unsigned8 is
   begin
      pragma Assert (AL_TEST = (AL_TEST and 16#FF#));
      return Unsigned8(AL_TEST and 16#FF#);
   end AL;

   procedure Write_AL(Val : in Unsigned8) is
   begin
      pragma Assert (Val = ((AL_TEST and 16#00#) or Val)); --@ASSERT:PASS
      AL_TEST := (AL_TEST and 16#00#) or Val;
   end Write_AL;

end X86;
