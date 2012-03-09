package Rec_Aggregate is

   type R1 is record
      X : Integer;
   end record;

   type R2 is record
      X, Y : Integer;
   end record;

   type R3 is record
      X : Integer;
      Y : Integer;
      Z : R2;
   end record;

   type R4 is record
      X : Integer;
      Y : Boolean;
   end record;

   One : Integer;

   procedure P1 (R : in out R1; B : Integer) with
     Pre => One = 1,
     Post => (case B is when 1      => R = (X => One),
	                when others => R = (others => One));

   procedure P2 (R : in out R2; B : Integer) with
     Pre => One = 1,
     Post => (case B is when 1 => R = (One, 2),
	                when 2 => R = (others => One),
	                when 3 => R = (One, others => One),
	                when 4 => R = (X => 2, others => One),
	                when others => R = (Y => 2, others => One));

   procedure P3 (R : in out R3; B : Integer) with
     Pre => One = 1,
     Post => (case B is when 1 => R = (One, 2, (One, 2)),
	                when 2 => R = (Z => (others => One), others => One),
	                when 3 => R = (One, Z => (1, others => One), others => One),
	                when 4 => R = (X => 2, Z => (X => 2, others => One), others => One),
	                when others => R = (Y => 2, Z => (Y => 2, others => One), others => One));

   function Ignore (R : R4) return Boolean is (True);

   procedure P4 (R : in out R4; B : Integer) with
     Pre => One = 1,
     Post => (case B is when 1 => R /= R4'(X => 2, Y => <>),
	                when 2 => Ignore ((others => <>)),
	                when 3 => R.X = One,
--	                when 4 => R.Y = True,
	                when others => Ignore((Y => <>, others => <>)));

end Rec_Aggregate;
