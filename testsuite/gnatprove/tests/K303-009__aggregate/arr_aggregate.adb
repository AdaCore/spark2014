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

   procedure P1_Bis (A : in out A1; B : Integer) is
   begin
      P1 (A, B);
   end P1_Bis;

   procedure P2_Bis (A : in out A2; B : Integer) is
   begin
      P2 (A, B);
   end P2_Bis;

   procedure P3_Bis (A : in out A3; B : Integer) is
   begin
      P3 (A, B);
   end P3_Bis;

   procedure P3_Ter (A : in out A3; B : Integer) is
      pragma SPARK_Mode (Off);  --  partially initialized aggregate
   begin
      case B is
	 when 1 =>
	    A := A3'((One, 2), others => <>);
	 when 2 =>
	    A := ((One, others => <>), (others => <>));
	 when 3 =>
	    A := A3'(others => <>);
	 when 4 =>
	    A := A3'(others => (2, others => <>));
	 when others =>
	    A := A3'(2 => (One, 2), others => <>);
      end case;
   end P3_Ter;
end Arr_Aggregate;
