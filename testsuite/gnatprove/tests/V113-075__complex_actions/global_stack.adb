package body Global_Stack
  with SPARK_Mode
is
   function is_zero (CHAR : in character) return BOOLEAN is
      zero : constant character := '0';
   begin
      return CHAR = '0';
   end is_zero;

   procedure too_complex is
   begin
      if char_in = 'c' then
         null;
      elsif is_zero (char_in) then
         null;
      end if;
   end too_complex;

end Global_Stack;
