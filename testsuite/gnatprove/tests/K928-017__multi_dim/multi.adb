package body Multi is

   procedure P4 (A : in out A4; B : Integer) is
   begin
      case B is
         when 1 =>
            A := ((One, 2), (One, 2));
         when 2 =>
            A := (others => (others => One));
         when 3 =>
            A := ((One, others => One), (others => One));
         when 4 =>
            A := ((1 => 2, others => One), (others => One));
         when others =>
            A := (2 => (2, One), others => (One, One));
      end case;
   end P4;
end Multi;
