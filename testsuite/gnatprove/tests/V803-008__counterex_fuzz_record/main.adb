procedure Main with SPARK_Mode is

  type Rec_1 is record
    A : Integer;
  end record;

  type Rec_2 is record
    A, B, C, D, E, F : Integer;
  end record;

  type Rec_3 is record
    A, B : Integer;
    C, D : Rec_1;
  end record;

  type Rec_4 is record
    A : Rec_1;
  end record;

  function "*" (Left, Right : Rec_1) return Rec_1 is ((A => Left.A * Right.A));

  function "*" (Left, Right : Rec_2) return Rec_2 is
    ((A => Left.A * Right.A,
      B => Left.B * Right.B,
      C => Left.C * Right.C,
      D => Left.D * Right.D,
      E => Left.E * Right.E,
      F => Left.F * Right.F));

  function "*" (Left, Right : Rec_3) return Rec_3 is
    ((Left.A * Right.A,
      Left.B * Right.B,
      Left.C * Right.C,
      Left.D * Right.D));

  function "*" (Left, Right : Rec_4) return Rec_4 is
    (A => (A => Left.A.A * Right.A.A));

  function Test_1 (R : Rec_1) return Integer with Unreferenced is
    Res : constant Rec_1 := R * R;
  begin
    pragma Assert (Res.A = 42);  --  @ASSERT:FAIL @COUNTEREXAMPLE
    return 42;
  end Test_1;

  function Test_2 (R : Rec_2) return Integer with Unreferenced is
    Res : constant Rec_2 := R * R;
  begin
    pragma Assert (Res.F = 42);  --  @ASSERT:FAIL @COUNTEREXAMPLE
    return 42;
  end Test_2;

  function Test_3 (R : Rec_3) return Integer with Unreferenced is
    Res : constant Rec_3 := R * R;
  begin
    pragma Assert (Res.A = Res.C.A);
    return 42;
  end Test_3;

  function Test_4 (R : Rec_4) return Integer with Unreferenced is
    Res : constant Rec_4 := R * R;
  begin
    pragma Assert (Res.A.A = 42);
    return 42;
  end Test_4;
begin
  null;
end Main;
