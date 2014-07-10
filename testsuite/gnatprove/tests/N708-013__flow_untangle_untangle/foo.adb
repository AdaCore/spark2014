package body Foo
is

   type R is record
      X : Integer;
      Y : Integer;
      Z : Integer;
   end record;

   type T is record
      F : R;
      G : R;
   end record;

   type Q (Found : Boolean) is record
      N : Integer;
   end record;

   type CArr is array (1 .. 5) of Integer;

   type Var_CArray is record
      N : Integer;
      A : CArr;
   end record;

   --  Sanity tests for 'Loop_Entry

   procedure Test_01 (N : out Integer)
   is
   begin
      N := 12;
      for I in Integer range 1 .. 3 loop
         N := N + 1;
         pragma Loop_Invariant (N > N'Loop_Entry);
      end loop;
   end Test_01;

   procedure Test_02 (N : Integer)
   is
      Tmp : R := (X => N,
                  Y => N,
                  Z => 0);
   begin
      for I in Integer range 1 .. 3 loop
         Tmp.Y := Tmp.Y + 1;
         pragma Loop_Invariant (Tmp.X'Loop_Entry = Tmp'Loop_Entry.X);
      end loop;
   end Test_02;

   --  Sanity tests for the new Untangle_Record_Field

   procedure Test_03 (A : Integer;
                      B : Integer;
                      O : out Integer)
   with Depends => (O => A, null => B)
   is
      Tmp : R;
   begin
      Tmp.X := A;
      O     := Tmp'Update (Y => B).X;
   end Test_03;

   procedure Test_04 (A : Integer;
                      B : Integer;
                      C : Integer;
                      O : out Integer)
   with Depends => (O => A, null => (B, C))
   is
      Tmp : T;
   begin
      Tmp.F.X := A;
      --Tmp.G   := Tmp.G'Update (Y => A);
      O       := Tmp'Update (G => (0, 0, B)).F'Update (Y => C,
                                                       Z => A + Tmp.F.X).X;
   end Test_04;

   procedure Test_05 (A : Integer;
                      B : Integer;
                      O : out Integer)
   with Depends => (O => A, null => B)
   is
      Tmp : R;
   begin
      Tmp.X := A;
      Tmp.Y := B;
      O     := Tmp.X;
   end Test_05;

   procedure Test_06 (A : out Q;
                      B : out Boolean)
   with Depends => (B => A, A => A)
   is
     Tmp_1 : constant Boolean := A.Found;
     Tmp_2 : Q (Tmp_1);
   begin
      case Tmp_2.Found is
         when True =>
            B := A.Found;
         when False =>
            B := A.Found;
      end case;
      A.N := 12;
   end Test_06;

   procedure Test_07 (A : Var_CArray;
                      O : out Integer)
   is
      Tmp : Var_CArray;
   begin
      Tmp.A := A.A'Update (1 => 2);
      O     := Tmp.A (3);
   end Test_07;

   procedure Test_08 (A : in out R;
                      B : Integer)
   is
   begin
      A := A'Update (X | Z => B);
   end Test_08;



end Foo;
