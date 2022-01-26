--  Multi-layered, nastier discriminant dependency relations
procedure Layered (Inp1, Inp2 : Natural;
                   Out1, Out2 : out Integer) with
  SPARK_Mode,
  Depends => (Out1 => Inp1, Out2 => Inp2)
  -- Contract is correct
is
   type T is record
      D1 : Integer;
      D2 : Integer := Inp2;
   end record;

   type U is record
      C : T;
   end record;

   type V is record
      B : U;
   end record;

   type W (I : Integer) is record
      A : V := (B => (C => (D1 => I - 1, others => <>)));
   end record;

   type X is record
      Z : W (Inp2);
   end record;

   Var : W (Inp1);
   Var2 : X;
begin
   Out1 := Var.A.B.C.D1;
   Out2 := Var2.Z.A.B.C.D1;
end;
