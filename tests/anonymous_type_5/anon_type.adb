package body Anon_Type is
   procedure To_Fix
   is
      T : Tab (0 .. 9);
      X : array (Integer range 0 .. 10) of Integer := (others => 0);
   begin
      T  := (others => 0);
   end To_Fix;
end Anon_Type;
