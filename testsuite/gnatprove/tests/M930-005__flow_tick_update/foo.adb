package body Foo
is

   type Coordinate_T is record
      X : Integer;
      Y : Integer;
      Z : Integer;
   end record;

   type Arr is array (1 .. 10) of Integer;

   --  procedure Test_01 (A, B, C : Integer;
   --                     D, E, F : out Integer)
   --  with Global => null,
   --       Depends => (D => A,
   --                   E => B,
   --                   F => C)
   --  is
   --     Tmp : Coordinate_T := (A, A, A);
   --  begin
   --     Tmp := Tmp'Update (Y => B,
   --                        Z => C);
   --     D := Tmp.X;
   --     E := Tmp.Y;
   --     F := Tmp.Z;
   --  end Test_01;

   procedure Test_02 (A          : in out Arr;
                      X, Y, Z, N : Integer;
                      W          : out Integer)
   with Global => null,
        Depends => (A => (A, X, Y, Z),
                    W => (A, X, Y, Z, N))
   is
   begin
      A := A'Update(4 => X,
                    Y => Z);
      W := A'Update(N => 3) (9);
   end Test_02;

end Foo;
