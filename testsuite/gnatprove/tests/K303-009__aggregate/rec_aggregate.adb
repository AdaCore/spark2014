package body Rec_Aggregate is
   procedure P1 (R : in out R1; B : Integer) is
   begin
      case B is
	 when 1 =>
	    R := (X => One);
	 when others =>
	    R := (others => One);
      end case;
   end P1;

   procedure P2 (R : in out R2; B : Integer) is
   begin
      case B is
	 when 1 =>
	    R := (One, 2);
	 when 2 =>
	    R := (others => One);
	 when 3 =>
	    R := (One, others => One);
	 when 4 =>
	    R := (X => 2, others => One);
	 when others =>
	    R := (Y => 2, others => One);
      end case;
   end P2;

   procedure P3 (R : in out R3; B : Integer) is
   begin
      case B is
	 when 1 =>
	    R := (One, 2, (One, 2));
	 when 2 =>
	    R := (Z => (others => One), others => One);
	 when 3 =>
	    R := (One, Z => (1, others => One), others => One);
	 when 4 =>
	    R := (X => 2, Z => (X => 2, others => One), others => One);
	 when others =>
	    R := (Y => 2, Z => (Y => 2, others => One), others => One);
      end case;
   end P3;

   procedure P4 (R : in out R4; B : Integer) is
      pragma SPARK_Mode (Off);  --  partially initialized aggregate
   begin
      case B is
	 when 1 =>
	    R := (One, True);
	 when 2 =>
	    R := (others => <>);
	 when 3 =>
	    R := (One, others => <>);
	 --  when 4 =>
	 --     R := (X => <>, others => True);
	 when others =>
	    R := (Y => <>, others => <>);
      end case;
   end P4;
end Rec_Aggregate;
