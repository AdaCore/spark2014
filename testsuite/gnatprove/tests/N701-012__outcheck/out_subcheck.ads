package Out_Subcheck is

   type Index_Type is range 0 .. 10;
   subtype Valid_Index_Type is Index_Type range 1 .. 10;

   procedure Read (Z : out Index_Type);

   function Read_Validate return Valid_Index_Type;
end Out_Subcheck;
