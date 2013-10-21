package body Test
is

   type DT is (Foo, Bar, Baz);

   type Wibble (D : DT) is record
      Flag : Boolean;
      case D is
         when Foo =>
            X : Integer;
         when Bar =>
            Y : Boolean;
         when Baz =>
            Z : DT;
      end case;
   end record;

   procedure Test_Init_01 (X : Integer;
                           R : out Wibble)
   is
   begin
      if X > 0 then
         R := (D    => Foo,
               X    => X,
               Flag => False);
      else
         R := (D    => Baz,
               Z    => Bar,
               Flag => False);
      end if;
   end Test_Init_01;

   procedure Test_Init_02 (R : out Wibble)
   is
      V : Wibble (Baz);
   begin
      V.Flag := True;
      --  Error - we have not initialised V.Z

      R := V;
   end Test_Init_02;

   procedure Test_Init_03 (R : out Wibble)
   is
      V : Wibble (Baz);
   begin
      V.Flag := True;
      V.Z    := Foo;

      R := V;
   end Test_Init_03;

   ----------------------------------------------------------------------

   type Array_2D is array (Integer range <>, Integer range <>) of Integer;

   type Matrix (C : Positive; R : Positive) is record
      Mat : Array_2D (1 .. C, 1 .. R);
   end record;

   subtype SquareMatrix4 is Matrix (4, 4);

   ----------------------------------------------------------------------

   type Failure_Reason is (Too_Lazy, Not_There, Dont_Care);

   type Search_Result (Found : Boolean := False) is record
      case Found is
         when True =>
            Index : Integer;
         when False =>
            Reason : Failure_Reason;
      end case;
   end record;

   --  We have a definite type, so as usual the discriminant is always
   --  initialized, but we can actually assign over a variable and
   --  change the discriminant

   procedure Test_Definite_01 (X : out Search_Result)
   is
   begin
      --  X.Found might be true or false, we don't care
      X := (Found => True,
            Index => 12);
   end Test_Definite_01;

   procedure Test_Definite_02 (X : out Search_Result)
   is
   begin
      --  Not necessarily wrong, but a flow error is issued here about
      --  X.Reason.
      X.Index := 12;
   end Test_Definite_02;

   procedure Test_Definite_03 (X : out Search_Result)
   is
   begin
      --  Again, not wrong, but flow errors again.
      case X.Found is
         when True =>
            X.Index := 12;
         when False =>
            X.Reason := Too_Lazy;
      end case;
   end Test_Definite_03;

   procedure Test_Definite_04 (X : out Search_Result)
   is
   begin
      --  Fixed version
      case X.Found is
         when True =>
            X := (True, 12);
         when False =>
            X := (False, Too_Lazy);
      end case;
   end Test_Definite_04;

   procedure Test_Definite_05 (X : out Search_Result)
   is
      R : Search_Result (X.Found);
   begin
      --  Technically, OK, but will raise a flow error again
      case R.Found is
         when True =>
            R.Index := 12;
         when False =>
            R := (False, Too_Lazy);
      end case;
      X := R;
   end Test_Definite_05;

   procedure Test_Definite_06 (X : out Search_Result;
                               Y : out Boolean)
   with Global => null,
        Depends => (X => null,
                    Y => X)
   is
   begin
      Y := X.Found;
      X := (False, Dont_Care);
   end Test_Definite_06;

   procedure Test_Definite_07 (X : out Search_Result;
                               Y : out Boolean)
   with Global => null,
        Depends => (X    => null,
                    Y    => null,
                    null => X)
   is
   begin
      Y := False;
      X := (False, Dont_Care);
   end Test_Definite_07;

   ----------------------------------------------------------------------

   --  A few tests involving non-discriminated record types in order
   --  to make sure the rewritten contract checking is OK.

   type ND_Record is record
      A : Integer;
      B : Integer;
      C : Integer;
   end record;

   procedure Test_ND_Record_01 (X, Y : Integer;
                                R    : out ND_Record)
   with Global  => null,
        Depends => (R => (X, Y))
   is
   begin
      R.A := X;
      R.B := 12;
      R.C := Y;
   end Test_ND_Record_01;

   procedure Test_ND_Record_02 (X, Y : Integer;
                                R    : in out ND_Record)
   with Global  => null,
        Depends => (R    => (X, Y),
                    null => R) --  R depends on R
   is
   begin
      R.A := X;
      R.C := Y;
   end Test_ND_Record_02;

   procedure Test_ND_Record_03 (X, Y : Integer;
                                R    : in out ND_Record)
   with Global  => null,
        Depends => (R =>+ (X, Y))
   is
   begin
      R.A := X;
      R.C := Y;
   end Test_ND_Record_03;

end Test;
