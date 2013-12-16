package MDA
  with SPARK_Mode => On
is
   type I is range 1 .. 10;
   type M is mod 8;
   type E is (Red, Green, Blue);

   type A2 is array (I, M) of Integer;
   type A3 is array (I, M, E) of Integer;

   type A2U is array (I range <>,
                      M range <>) of Integer;

   type A3U is array (I range <>,
                      M range <>,
                      E range <>) of Integer;


   ----------------------------------------------------------------------------
   -- Set one element of multidimensional arrays
   ----------------------------------------------------------------------------

   --  Updating one element of two-dimensional constrained array
   procedure Set2C (A : in out A2;
                    X : in I;
                    Y : in M;
                    V : in Integer)
     with Depends => (A => (A, X, Y, V)),
          Post => A = A'Old'Update ((X, Y) => V);

   --  Updating one element of two-dimensional unconstrained array
   procedure Set2U (A : in out A2U;
                    X : in I;
                    Y : in M;
                    V : in Integer)
     with Depends => (A => (A, X, Y, V)),
          Pre  => X in A'Range (1) and
                  Y in A'Range (2),
          Post => A = A'Old'Update ((X, Y) => V);

   --  Updating one element of three-dimensional constrained array
   procedure Set3C (A : in out A3;
                    X : in I;
                    Y : in M;
                    Z : in E;
                    V : in Integer)
     with Depends => (A => (A, X, Y, Z, V)),
          Post => A = A'Old'Update ((X, Y, Z) => V);

   --  Updating one element of three-dimensional unconstrained array
   procedure Set3U (A : in out A3U;
                    X : in I;
                    Y : in M;
                    Z : in E;
                    V : in Integer)
     with Depends => (A => (A, X, Y, Z, V)),
          Pre  => X in A'Range (1) and
                  Y in A'Range (2) and
                  Z in A'Range (3),
          Post => A = A'Old'Update ((X, Y, Z) => V);

   ----------------------------------------------------------------------------
   -- Set two non-overlapping elements of multidimensional arrays
   ----------------------------------------------------------------------------

   --  Updating two elements of two-dimensional constrained arrays
   procedure Set2E2C (A  : in out A2;
                      X1 : in I;
                      Y1 : in M;
                      X2 : in I;
                      Y2 : in M;
                      V1 : in Integer;
                      V2 : in Integer)
     with Depends => (A => (A, X1, Y1, V1, X2, Y2, V2)),
          Post => A = A'Old'Update ((X1, Y1) => V1, (X2, Y2) => V2);

   --  Updating two elements of two-dimensional unconstrained arrays
   procedure Set2E2U (A  : in out A2U;
                      X1 : in I;
                      Y1 : in M;
                      X2 : in I;
                      Y2 : in M;
                      V1 : in Integer;
                      V2 : in Integer)
     with Depends => (A => (A, X1, Y1, V1, X2, Y2, V2)),
          Pre  => X1 in A'Range (1) and
                  Y1 in A'Range (2) and
                  X2 in A'Range (1) and
                  Y2 in A'Range (2),
          Post => A = A'Old'Update ((X1, Y1) => V1, (X2, Y2) => V2);

   --  Updating two elements of three-dimensional constrained arrays
   procedure Set2E3C (A  : in out A3;
                      X1 : in I;
                      Y1 : in M;
                      Z1 : in E;
                      X2 : in I;
                      Y2 : in M;
                      Z2 : in E;
                      V1 : in Integer;
                      V2 : in Integer)
     with Depends => (A => (A, X1, Y1, Z1, V1, X2, Y2, Z2, V2)),
          Post => A = A'Old'Update ((X1, Y1, Z1) => V1, (X2, Y2, Z2) => V2);

   --  Updating two elements of three-dimensional unconstrained arrays
   procedure Set2E3U (A  : in out A3U;
                      X1 : in I;
                      Y1 : in M;
                      Z1 : in E;
                      X2 : in I;
                      Y2 : in M;
                      Z2 : in E;
                      V1 : in Integer;
                      V2 : in Integer)
     with Depends => (A => (A, X1, Y1, Z1, V1, X2, Y2, Z2, V2)),
          Pre  => X1 in A'Range (1) and
                  Y1 in A'Range (2) and
                  Z1 in A'Range (3) and
                  X2 in A'Range (1) and
                  Y2 in A'Range (2) and
                  Z2 in A'Range (3),
          Post => A = A'Old'Update ((X1, Y1, Z1) => V1, (X2, Y2, Z2) => V2);


end MDA;
