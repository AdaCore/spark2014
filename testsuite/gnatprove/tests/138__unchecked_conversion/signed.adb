with Ada.Unchecked_Conversion;

procedure Signed is

   type S32 is range -2**31 .. 2**31-1;

   type R1 is record
      A : S32;
   end record;
   for R1 use record
      A at 0 range 0..31;
   end record;

   function To_Rec1 is new Ada.Unchecked_Conversion (Source => S32, Target => R1);
   function Of_Rec1 is new Ada.Unchecked_Conversion (Source => R1, Target => S32);

   procedure Test_R1 (X : S32; Y : R1)
     with Global => null
   is
      Conv_X : constant R1 := To_Rec1 (X);
      Conv_Y : constant S32 := Of_Rec1 (Y);
   begin
      pragma Assert (Conv_X.A = X);
      pragma Assert (Of_Rec1 (Conv_X) = X);

      pragma Assert (Conv_Y = Y.A);
      pragma Assert (To_Rec1 (Conv_Y) = Y);
   end;

   ------

   type S1 is range -2**0 .. 2**0-1;
   type S2 is range -2**1 .. 2**1-1;
   type S3 is range -2**2 .. 2**2-1;
   type S4 is range -2**3 .. 2**3-1;
   type S5 is range -2**4 .. 2**4-1;
   type S6 is range -2**5 .. 2**5-1;
   type S7 is range -2**6 .. 2**6-1;

   type R2 is record
      A : S1;
      B : S2;
      C : S3;
      D : S4;
      E : S5;
      F : S6;
      G : S7;
      H : S4;
   end record;
   for R2 use record
      A at 0 range 0..0;
      B at 0 range 1..2;
      C at 0 range 3..5;
      D at 0 range 6..9;
      E at 0 range 10..14;
      F at 0 range 15..20;
      G at 0 range 21..27;
      H at 0 range 28..31;
   end record;

   function To_Rec2 is new Ada.Unchecked_Conversion (Source => S32, Target => R2);
   function Of_Rec2 is new Ada.Unchecked_Conversion (Source => R2, Target => S32);

   procedure Test_R2 (X : S32; Y : R2)
     with Global => null
   is
      Conv_X : constant R2 := To_Rec2 (X);
      Conv_Y : constant S32 := Of_Rec2 (Y);
   begin
      if X = -1 then
	 pragma Assert (Conv_X.A = -1);
	 pragma Assert (Conv_X.B = -1);
	 pragma Assert (Conv_X.C = -1);
	 pragma Assert (Conv_X.D = -1);
	 pragma Assert (Conv_X.E = -1);
	 pragma Assert (Conv_X.F = -1);
	 pragma Assert (Conv_X.G = -1);
      elsif X = S32'Last then
	 pragma Assert (Conv_X.A = -1);
	 pragma Assert (Conv_X.B = -1);
	 pragma Assert (Conv_X.C = -1);
	 pragma Assert (Conv_X.D = -1);
	 pragma Assert (Conv_X.E = -1);
	 pragma Assert (Conv_X.F = -1);
	 pragma Assert (Conv_X.G = S7'Last);
      end if;
      pragma Assert (Of_Rec2 (Conv_X) = X);

      if Y.A = -1
	and Y.B = -1
	and Y.C = -1
	and Y.D = -1
	and Y.E = -1
	and Y.F = -1
	and Y.G = -1
      then
	 pragma Assert (Conv_Y = -1);
      end if;
      pragma Assert (To_Rec2 (Conv_Y) = Y);
   end;


begin
   Test_R1 (S32'First, R1'(A => S32'Last));

   Test_R2 (-1, R2'(A => -1,
		    B => -1,
		    C => -1,
		    D => -1,
		    E => -1,
		    F => -1,
		    G => -1,
		    H => -1));

end;
