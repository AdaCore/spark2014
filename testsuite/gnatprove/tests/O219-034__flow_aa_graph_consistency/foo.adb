package body Foo
is

   type T is record
      F  : Integer;
      F2 : Integer;
      F3 : Integer;
      F4 : Integer;
      F5 : Integer;  --  without this, test3 passes and test2 does not
   end record;

   Null_Record : constant T := (0, 0, 0, 0, 0);

   procedure P (A, B : Integer;
                X, Y : out T)
   with Global => null,
        Depends => (X => A,
                    Y => B)
   is
   begin
      X := Null_Record;
      Y := Null_Record;

      Y.F := B;
      X.F := A; -- swapping these make test3 pass and test2 not
   end P;

   procedure Test_01 (A, B : Integer;
                      C    : out Integer)
   is
      R : T;
   begin
      P (A, B, R, R);
      C := R.F;
   end Test_01;

   procedure Test_02 (A, B : Integer;
                      C    : out Integer)
   is
      R : T;
   begin
      P (A, B, R, R);
      C := R.F;
   end Test_02;

   procedure Test_03 (A, B : Integer;
                      C    : out Integer)
   is
      R : T;
   begin
      P (A, B, R, R);
      C := R.F;
   end Test_03;

end Foo;
