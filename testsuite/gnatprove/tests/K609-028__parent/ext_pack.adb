package body Ext_Pack with
  Refined_State => (S => Step)
is

   Step : Integer := 0;

   procedure Result is
   begin
      C := C + Step;
      Step := Step + 1;
   end Result;

end Ext_Pack;
