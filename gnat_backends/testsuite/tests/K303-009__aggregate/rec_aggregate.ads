package Rec_Aggregate is
   pragma Annotate (Gnatprove, Force);
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
   
   procedure P1 (R : in out R1; B : Integer) with
     Post => (case B is when 1      => R = (X => 1),
	                when others => R = (others => 1));

   procedure P2 (R : in out R2; B : Integer) with
     Post => (case B is when 1 => R = (1, 2),
	                when 2 => R = (others => 1),
	                when 3 => R = (1, others => 1),
	                when 4 => R = (X => 2, others => 1),
	                when others => R = (Y => 2, others => 1));
     
   procedure P3 (R : in out R3; B : Integer) with
     Post => (case B is when 1 => R = (1, 2, (1, 2)),
	                when 2 => R = (Z => (others => 1), others => 1),
	                when 3 => R = (1, Z => (1, others => 1), others => 1),
	                when 4 => R = (X => 2, Z => (X => 2, others => 1), others => 1),
	                when others => R = (Y => 2, Z => (Y => 2, others => 1), others => 1));
	
   function Ignore (R : R4) return Boolean is (True);
	
   procedure P4 (R : in out R4; B : Integer) with
     Post => (case B is when 1 => R = (1, True),
	                when 2 => Ignore ((others => <>)),
	                when 3 => R.X = 1,
--	                when 4 => R.Y = True,
	                when others => Ignore((Y => <>, others => <>)));

end Rec_Aggregate;
