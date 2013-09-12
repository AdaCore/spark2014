package Arr_Aggregate is

   type A1 is array (1 .. 1) of Integer;
   type A2 is array (1 .. 2) of Integer;
   type A3 is array (1 .. 2) of A2;

   One : Integer;

   procedure P1 (A : in out A1; B : Integer) with
     Pre => One = 1,
     Post => (case B is when 1      => A (One) = One,
   	                when others => (for all K in A1'Range => A (K) = One));

   procedure P2 (A : in out A2; B : Integer) with
     Pre => One = 1,
     Post => (case B is when 1 => A (One'Old) = One'Old and A (2) = 2,
   	                when 2 => (for all K in A2'Range => A (K) = One'Old),
   	                when 3 => (for all K in A2'Range => A (K) = One),
   	                when 4 => A (One) = 2 and A (2) = One,
   	                when others => A (One) = One and A (2) = 2);

   procedure P3 (A : in out A3; B : Integer) with
     Pre => One = 1,
     Post => (case B is when 1 => (for all J in A3'Range => (A (J) (One) = One and A (J) (2) = 2)),
	                when 2 => (for all J in A3'Range => (for all K in A2'Range => A (J) (K) = One)),
	                when 3 => (for all J in A3'Range => (for all K in A2'Range => A (J) (K) = One)),
	                when 4 => (for all J in A3'Range => (A (J) (One) = 2 and A (J) (2) = One)),
	                when others => (for all J in A3'Range => (A (J) (One'Old) = One'Old and A (J) (2) = 2)));

   procedure P1_Bis (A : in out A1; B : Integer) with
     Pre => One = 1,
     Post => (case B is when 1      => A = (1 => One),
   	                when others => A = (1 => One));

   procedure P2_Bis (A : in out A2; B : Integer) with
     Pre => One = 1,
     Post => (case B is when 1 => A = (One, 2),
   	                when 2 => A = (One, One),
   	                when 3 => A = (One, One),
   	                when 4 => A = (2, One),
   	                when others => A = (One, 2));

   procedure P3_Bis (A : in out A3; B : Integer) with
     Pre => One = 1,
     Post => (case B is when 1 => A = ((One, 2), (One, 2)),
	                when 2 => A = ((One, One), (One'Old, One)),
	                when 3 => A = ((One, One), (One, One)),
	                when 4 => A = ((2, One), (2, One)),
	                when others => A = ((One, 2), (One, 2)));

   procedure P3_Ter (A : in out A3; B : Integer) with
     SPARK_Mode => Off,  --  partially initialized aggregate
     Pre => One = 1,
     Post => (case B is when 1 => A = A3'((One, 2), others => <>),
	                when 2 => A = ((One, others => <>), (others => <>)),
	                when 3 => A = A3'(others => <>),
	                when 4 => A = A3'(others => (2, others => <>)),
	                when others => A = A3'(2 => (One, 2), others => <>));

end Arr_Aggregate;
