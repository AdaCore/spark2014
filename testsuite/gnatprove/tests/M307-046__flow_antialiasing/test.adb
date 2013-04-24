package body Test
is

   type Record_A is record
      A : Boolean;
      B : Boolean;
      C : Boolean;
   end record;

   type Array_T is array (Natural) of Record_A;

   type Record_B is record
      A : Array_T;
      B : Integer;
      C : Boolean;
      D : Record_A;
   end record;

   Global_RA : Record_A;

   procedure Op_R1 (X : in out Record_A;
                    Y : in out Record_A)
   is
   begin
      X.A := Y.B;
      Y.B := X.C;
   end Op_R1;

   procedure Op_R1 (X : in out Record_A)
   with Global => (In_Out => Global_RA)
   is
   begin
      X.A := Global_RA.B;
      Global_RA.B := X.C;
   end Op_R1;

   procedure Op_R1_B (X : Record_A;
                      Y : Record_A;
                      Z : out Record_A)
   is
   begin
      Z.A := X.A and Y.A;
      Z.B := X.B or Y.B;
      Z.C := X.C xor Y.C;
   end Op_R1_B;

   procedure Op_R2 (X : in out Record_B;
                    Y : in     Record_B)
   is
   begin
      X.C := X.B = Y.B;
   end Op_R2;

   procedure Op_R3 (X : in out Record_B;
                    Y : in out Record_A)
   is
   begin
      Y.A := False;
      X.D := Y;
   end Op_R3;

   procedure Op_R4 (X : in out Record_A;
                    Y : in out Boolean)
   is
   begin
      X.A := Y;
      Y := X.B;
   end Op_R4;

   procedure Op_String_IO_I (X : in out String;
                        Y : String)
   is
   begin
      X (1) := Y (Y'Last);
   end Op_String_IO_I;


   procedure Test_01 (X : in out Record_A)
   is
   begin
      Op_R1 (X, X);  --  Illegal
   end Test_01;

   procedure Test_02 (X : in out Record_A)
   is
   begin
      Op_R1 (X);  --  OK
   end Test_02;

   procedure Test_03
   is
   begin
      Op_R1 (Global_RA);  --  Illegal
   end Test_03;

   procedure Test_04 (X : in out Record_A)
   with Global => (Output => Global_RA)
   is
   begin
      Op_R1_B (X, X, Global_RA);  --  OK
   end Test_04;

   procedure Test_05 (X : in out Record_A)
   with Global => (In_Out => Global_RA)
   is
   begin
      Op_R1_B (X, Global_RA, Global_RA);  --  Illegal
   end Test_05;

   procedure Test_06 (X : in out Record_B)
   is
   begin
      Op_R3 (X, X.D); -- Illegal
   end Test_06;

   procedure Test_07 (X : in out Record_B)
   is
      Y : Record_A := X.D;
   begin
      Op_R3 (X, Y); -- OK
   end Test_07;

   procedure Test_08 (X : in out Record_B)
   is
      Y : Record_A renames X.D;
   begin
      Op_R3 (X, Y); -- Illegal
   end Test_08;

   procedure Test_09 (X : in out Record_B)
   is
   begin
      Op_R4 (X.D, X.D.B); -- Illegal
   end Test_09;

   procedure Test_10 (X : in out Record_B)
   is
   begin
      Op_R4 (X.D, X.C); -- OK
   end Test_10;

   procedure Test_11 (X : in out Record_B)
   is
   begin
      Op_R1 (X.A (5), X.A (2)); --  OK
   end Test_11;

   procedure Test_12 (X : in out Record_B)
   is
   begin
      Op_R1 (X.A (5), X.A (2 + 3)); --  Illegal
   end Test_12;

   procedure Test_13 (X    : in out Record_B;
                      I, J : Natural)
   is
   begin
      Op_R1 (X.A (I), X.A (J)); --  Needs proof
   end Test_13;

   ----------------------------------------------------------------------
   --  Slices
   ----------------------------------------------------------------------

   procedure Slice_01 (S : in out String)
   is
   begin
      Op_String_IO_I (S (2 .. 5), S (1 .. 1));  -- OK
   end Slice_01;

   procedure Slice_02 (A : in out String;
                       B : in out String)
   is
   begin
      Op_String_IO_I (A (1 .. 3), B (1 .. 3)); --  OK
   end Slice_02;

   procedure Slice_03 (A : in out String;
                       N : Positive)
   is
   begin
      Op_String_IO_I (A (1 .. N), A (N .. A'Last)); --  Illegal
   end Slice_03;

   procedure Slice_04 (A : in out String;
                       N : Positive)
   is
   begin
      Op_String_IO_I (A (1 .. N), A (N + 1 .. A'Last)); --  OK
   end Slice_04;

   procedure Slice_05 (A : in out String;
                       N : Positive;
                       M : Positive)
   is
   begin
      Op_String_IO_I (A (N .. N), A (M .. M)); --  OK
   end Slice_05;

   --  TODO: Unchecked conversion "renaming"

   --  TODO: Type/view conversion


end Test;
