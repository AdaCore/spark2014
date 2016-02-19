package Regpat is

   type Program_Data is array (Integer range <>) of Character;

   type Pattern_Matcher is record
      Program : Program_Data (1 .. 16) := (others => ASCII.NUL);
   end record;

   procedure Match (Self : Pattern_Matcher);

end Regpat;
