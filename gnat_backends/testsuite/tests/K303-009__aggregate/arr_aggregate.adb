package body Arr_Aggregate is
   procedure P1 (A : in out A1; B : Integer) is
   begin
      case B is
   	 when 1 =>
   	    A := (1 => One);
   	 when others =>
   	    A := (others => One);
      end case;
   end P1;
   
   procedure P2 (A : in out A2; B : Integer) is
   begin
      case B is
   	 when 1 =>
   	    A := (One, 2);
   	 when 2 =>
   	    A := (others => One);
   	 when 3 =>
   	    A := (One, others => One);
   	 when 4 =>
   	    A := (1 => 2, others => One);
   	 when others =>
   	    A := (2 => 2, others => One);
      end case;
   end P2;
   
   procedure P3 (A : in out A3; B : Integer) is
   begin
      case B is
	 when 1 =>
	    A := ((One, 2), (One, 2));
	 when 2 =>
	    A := (2 => (others => One), others => (others => One));
	 when 3 =>
	    A := ((One, others => One), (1, others => One));
	 when 4 =>
	    A := (1 => (1 => 2, others => One), 2 => (1 => 2, others => One));
	 when others =>
	    A := (2 => (2, others => One), 1 => (2 => 2, others => One));
      end case;
   end P3;
end Arr_Aggregate;
