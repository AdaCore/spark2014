package body Out_Subcheck is

   procedure Read (Z : out Index_Type) is
   begin
      Z := 0;
   end Read;

   function Read_Validate return Valid_Index_Type is
      X : Valid_Index_Type;
   begin
      Read (X); --@RANGE_CHECK:FAIL
      return X;
   end Read_Validate;

end Out_Subcheck;
