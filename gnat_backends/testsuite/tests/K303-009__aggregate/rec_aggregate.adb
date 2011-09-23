package body Rec_Aggregate is
   procedure P1 (R : in out R1; B : Integer) is
   begin
      case B is
	 when 1 =>
	    R := (X => 1);
	 when others =>
	    R := (others => 1);
      end case;
   end P1;

   procedure P2 (R : in out R2; B : Integer) is
   begin
      case B is
	 when 1 =>
	    R := (1, 2);
	 when 2 =>
	    R := (others => 1);
	 when 3 =>
	    R := (1, others => 1);
	 when 4 =>
	    R := (X => 2, others => 1);
	 when others =>
	    R := (Y => 2, others => 1);
      end case;
   end P2;
   
   procedure P3 (R : in out R3; B : Integer) is
   begin
      case B is
	 when 1 =>
	    R := (1, 2, (1, 2));
	 when 2 =>
	    R := (Z => (others => 1), others => 1);
	 when 3 =>
	    R := (1, Z => (1, others => 1), others => 1);
	 when 4 =>
	    R := (X => 2, Z => (X => 2, others => 1), others => 1);
	 when others =>
	    R := (Y => 2, Z => (Y => 2, others => 1), others => 1);
      end case;
   end P3;
   
   procedure P4 (R : in out R4; B : Integer) is
   begin
      case B is
	 when 1 =>
	    R := (1, True);
	 when 2 =>
	    R := (others => <>);
	 when 3 =>
	    R := (1, others => <>);
	 --  when 4 =>
	 --     R := (X => <>, others => True);
	 when others =>
	    R := (Y => <>, others => <>);
      end case;
   end P4;
end Rec_Aggregate;
