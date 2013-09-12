package body Ext_Pack is 
   
   Step : Integer := 0;
   
   procedure Result is
   begin
      C := C + Step;
      Step := Step + 1;
   end Result;

end Ext_Pack;
