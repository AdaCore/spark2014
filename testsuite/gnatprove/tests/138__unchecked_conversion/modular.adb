with Ada.Unchecked_Conversion;

procedure Modular is

   type U32 is mod 2**32;

   type R1 is record
      A : U32;
   end record;
   for R1 use record
      A at 0 range 0..31;
   end record;

   function To_Rec1 is new Ada.Unchecked_Conversion (Source => U32, Target => R1);
   function Of_Rec1 is new Ada.Unchecked_Conversion (Source => R1, Target => U32);

   procedure Test_R1 (X : U32; Y : R1)
     with Global => null
   is
      Conv_X : constant R1 := To_Rec1 (X);
      Conv_Y : constant U32 := Of_Rec1 (Y);
   begin
      pragma Assert (Conv_X.A = X);
      pragma Assert (Of_Rec1 (Conv_X) = X);

      pragma Assert (Conv_Y = Y.A);
      pragma Assert (To_Rec1 (Conv_Y) = Y);
   end;

   ------

   type U1 is mod 2**1;
   type U2 is mod 2**2;
   type U3 is mod 2**3;
   type U4 is mod 2**4;
   type U5 is mod 2**5;
   type U6 is mod 2**6;
   type U7 is mod 2**7;

   type R2 is record
      A : U1;
      B : U2;
      C : U3;
      D : U4;
      E : U5;
      F : U6;
      G : U7;
      H : U4;
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

   function To_Rec2 is new Ada.Unchecked_Conversion (Source => U32, Target => R2);
   function Of_Rec2 is new Ada.Unchecked_Conversion (Source => R2, Target => U32);

   procedure Test_R2 (X : U32; Y : R2)
     with Global => null
   is
      Conv_X : constant R2 := To_Rec2 (X);
      Conv_Y : constant U32 := Of_Rec2 (Y);
   begin
      pragma Assert (U32(Conv_X.A) = ((X / 2**0) and (2**1 - 1)));
      pragma Assert (U32(Conv_X.B) = ((X / 2**1) and (2**2 - 1)));
      pragma Assert (U32(Conv_X.C) = ((X / 2**3) and (2**3 - 1)));
      pragma Assert (U32(Conv_X.D) = ((X / 2**6) and (2**4 - 1)));
      pragma Assert (U32(Conv_X.E) = ((X / 2**10) and (2**5 - 1)));
      pragma Assert (U32(Conv_X.F) = ((X / 2**15) and (2**6 - 1)));
      pragma Assert (U32(Conv_X.G) = ((X / 2**21) and (2**7 - 1)));
      pragma Assert (U32(Conv_X.H) = ((X / 2**28) and (2**4 - 1)));
      pragma Assert (Of_Rec2 (Conv_X) = X);

      pragma Assert (Conv_Y = U32(Y.A)
		            + U32(Y.B) * 2**1
		            + U32(Y.C) * 2**3
		            + U32(Y.D) * 2**6
		            + U32(Y.E) * 2**10
		            + U32(Y.F) * 2**15
		            + U32(Y.G) * 2**21
		            + U32(Y.H) * 2**28);
      pragma Assert (To_Rec2 (Conv_Y) = Y);
   end;

   ------

   type R3 is record
      A : U5;
   end record with Size => 5;
   for R3 use record
      A at 0 range 0..4;
   end record;

   type R4 is record
      B : R3;
      C : U7;
      D : U4;
   end record with Size => 16;
   for R4 use record
      B at 0 range 0..4;
      C at 0 range 5..11;
      D at 0 range 12..15;
   end record;

   type A4 is array (1 .. 2) of R4 with Pack, Size => 32;

   type R5 is record
      E : A4;
   end record with Size => 32;
   for R5 use record
      E at 0 range 0..31;
   end record;

   function To_Rec5 is new Ada.Unchecked_Conversion (Source => U32, Target => R5);
   function Of_Rec5 is new Ada.Unchecked_Conversion (Source => R5, Target => U32);

   procedure Test_R5 (X : U32; Y : R5)
     with Global => null
   is
      Conv_X : constant R5 := To_Rec5 (X);
      Conv_Y : constant U32 := Of_Rec5 (Y);
   begin
      pragma Assert (U32(Conv_X.E(1).B.A) = ((X / 2**0) and (2**5 - 1)));
      pragma Assert (U32(Conv_X.E(1).C)   = ((X / 2**5) and (2**7 - 1)));
      pragma Assert (U32(Conv_X.E(1).D)   = ((X / 2**12) and (2**4 - 1)));
      pragma Assert (U32(Conv_X.E(2).B.A) = ((X / 2**16) and (2**5 - 1)));
      pragma Assert (U32(Conv_X.E(2).C)   = ((X / 2**21) and (2**7 - 1)));
      pragma Assert (U32(Conv_X.E(2).D)   = ((X / 2**28) and (2**4 - 1)));
      pragma Assert (Of_Rec5 (Conv_X) = X);

      pragma Assert (Conv_Y = U32(Y.E(1).B.A)
		            + U32(Y.E(1).C) * 2**5
		            + U32(Y.E(1).D) * 2**12
		            + U32(Y.E(2).B.A) * 2**16
		            + U32(Y.E(2).C) * 2**21
		            + U32(Y.E(2).D) * 2**28);
      pragma Assert (To_Rec5 (Conv_Y) = Y);
   end;

   ------

   function Rec2_To_Rec5 is new Ada.Unchecked_Conversion (Source => R2, Target => R5);
   function Rec5_To_Rec2 is new Ada.Unchecked_Conversion (Source => R5, Target => R2);

   procedure Test_R2_R5 (X : R2; Y : R5)
     with Global => null
   is
      Conv_X : constant R5 := Rec2_To_Rec5 (X);
      Conv_Y : constant R2 := Rec5_To_Rec2 (Y);
   begin
      pragma Assert (Rec5_To_Rec2 (Conv_X) = X);
      pragma Assert (Rec2_To_Rec5 (Conv_Y) = Y);
   end;

   ------

   Var2 : constant R2 :=
     R2'(A => U1'Last,
	 B => U2'Last,
	 C => U3'Last,
	 D => U4'Last,
	 E => U5'Last,
	 F => U6'Last,
	 G => U7'Last,
	 H => U4'Last);

   Var5 : R5 :=
     (E => A4'(1 => R4'(B => R3'(A => U5'Last),
			C => U7'Last,
			D => U4'Last),
	       2 => R4'(B => R3'(A => U5'Last),
			C => U7'Last,
			D => U4'Last)));

   ------

   package P is
      type P2 is private;
      type P5 is private;
      V2 : constant P2;
      V5 : constant P5;
   private
      type P2 is new R2;
      type P5 is new R5;
      V2 : constant P2 := P2(Var2);
      V5 : constant P5 := P5(Var5);
   end;
   use P;

   function P2_To_P5 is new Ada.Unchecked_Conversion (Source => P2, Target => P5);
   function P5_To_P2 is new Ada.Unchecked_Conversion (Source => P5, Target => P2);

   procedure Test_P2_P5 (X : P2; Y : P5)
     with Global => null
   is
      Conv_X : constant P5 := P2_To_P5 (X);
      Conv_Y : constant P2 := P5_To_P2 (Y);
   begin
      pragma Assert (P5_To_P2 (Conv_X) = X);
      pragma Assert (P2_To_P5 (Conv_Y) = Y);
   end;

   ------

   package Q is
      type P32 is private;
      function Of_U32 (U : U32) return P32;
   private
      type P32 is mod 2**32;
      function Of_U32 (U : U32) return P32 is (P32(U));
   end Q;
   use Q;

   type P1 is record
      A : P32;
   end record;
   for P1 use record
      A at 0 range 0..31;
   end record;

   function To_P1 is new Ada.Unchecked_Conversion (Source => P32, Target => P1);
   function Of_P1 is new Ada.Unchecked_Conversion (Source => P1, Target => P32);

   procedure Test_P1 (X : P32; Y : P1)
     with Global => null
   is
      Conv_X : constant P1 := To_P1 (X);
      Conv_Y : constant P32 := Of_P1 (Y);
   begin
      pragma Assert (Conv_X.A = X);
      pragma Assert (Of_P1 (Conv_X) = X);

      pragma Assert (Conv_Y = Y.A);
      pragma Assert (To_P1 (Conv_Y) = Y);
   end;

begin
   Test_R1 (0, R1'(A => U32'Last));

   Test_R2 (42, Var2);

   Test_R5 (42, Var5);

   Test_R2_R5 (Var2, Var5);

   Test_P2_P5 (V2, V5);

   Test_P1 (Of_U32(0), P1'(A => Of_U32(U32'Last)));
end;
