package body Handling is

   function Dummy return Boolean is (True);

   function Is_Digit return Boolean renames Dummy;

   function Is_Hexadecimal_Digit return Boolean is (Is_Digit);

end Handling;
