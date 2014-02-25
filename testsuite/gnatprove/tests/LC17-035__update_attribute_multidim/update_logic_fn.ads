package Update_Logic_Fn
  with SPARK_Mode => On
is

   type I is range 1 .. 10;
   type M is mod 8;
   type E is (Red, Green, Blue);

   type A2 is array (I, M) of Integer;
   type A3 is array (I, M, E) of Integer;

   A_2D_Arr : constant A2 := A2'(others => (others => 100 ));
   A_3D_Arr : constant A3 := A3'(others => (others => (others => 1000)));

   ----------------------------------------------------------------------------
   --  'Update exercise: different prefixes, choice lists, overlaps etc.:
   ----------------------------------------------------------------------------

   --  Update of two-dim constrained array constant, possibly overlapping
   --  choices, Postcondition is valid, uses 'Update expression, fully
   --  specified.

   procedure P1 (A  : out A2;
                 X  : in I;
                 Y  : in M;
                 V1 : in Integer;
                 V2 : in Integer)
     with Depends => (A => (X, Y, V1, V2)),
     Post => (A = A_2D_Arr'Update ((5, 7) => V1, (X, Y) => V2));

   --  Same as above, different body. Valid postcondition.

   procedure P2 (A  : out A2;
                 X  : in I;
                 Y  : in M;
                 V1 : in Integer;
                 V2 : in Integer)
     with Depends => (A => (X, Y, V1, V2)),
     Post => (A = A_2D_Arr'Update ((5, 7) => V1, (X, Y) => V2));

   --  Same as above. Falsifiable postcondition.

   procedure P2_False (A  : out A2;
                       X  : in I;
                       Y  : in M;
                       V1 : in Integer;
                       V2 : in Integer)
     with Depends => (A => (X, Y, V1, V2)),
     Post => (A = A_2D_Arr'Update ((4, 7) => V1, (X, Y) => V2));

   --  Update of three-dim constrained array constant, possibly overlapping
   --  choices. Valid postcondition. Postcondition uses 'Update expression,
   --  fully specified.

   procedure P3 (A  : out A3;
                 X  : in I;
                 Y  : in M;
                 Z  : in E;
                 V1 : in Integer;
                 V2 : in Integer)
     with Depends => (A => (X, Y, Z, V1, V2)),
     Post => (A = A3'(others => (others => (others => 1000 )))
                'Update ((5, 7, Green) => V1,
                         (X, Y, Z)     => V2));

   --  Same as above. Falsifiable postcondition.

   procedure P3_False (A  : out A3;
                       X  : in I;
                       Y  : in M;
                       Z  : in E;
                       V1 : in Integer;
                       V2 : in Integer)
     with Depends => (A => (X, Y, Z, V1, V2)),
     Post => (A = A3'(others => (others => (others => 1000 )))
                'Update ((5, 7, Green) => V1,
                         (X, Y, Blue)  => V2));

   --  For reference, same example as above: Update of two-dim constrained
   --  array, overlapping choices, Postcondition uses normal aggregate,
   --  partial specification. Postcondition valid.

   procedure P4 (A  : out A2;
                 X  : in I;
                 Y  : in M;
                 V1 : in Integer;
                 V2 : in Integer)
     with Depends => (A => (X, Y, V1, V2)),
     Post => (if X = 5 and Y = 7 then
                A = A2'(5      => (7 => V2, others => 1000),
                        others => (others => 1000)));

   --  For reference, same example as above: Update of two-dim constrained
   --  array, overlapping choices, Postcondition uses set of implications,
   --  partial specification. Postcondition valid.

   procedure P5 (A  : out A2;
                 X  : in I;
                 Y  : in M;
                 V1 : in Integer;
                 V2 : in Integer)
     with Depends => (A => (X, Y, V1, V2)),
     Post => ((if X = 5  and Y = 7  then A (5, 7) = V2) and
              (if X = 5  and Y /= 7 then A (5, 7) = V1  and A (5, Y) = V2) and
              (if X /= 5 and Y = 7  then A (5, 7) = V1  and A (X, 7) = V2) and
              (if X /= 5 and Y /= 7 then A (5, 7) = V1  and A (X, Y) = V2));

   --  Update of two-dimensional array constant, choice list, possible
   --  overlap. Postcondition valid.

   procedure P6 (A  : out A2;
                 X  : in I;
                 Y  : in M;
                 V1 : in Integer)
     with Depends => (A => (X, Y, V1)),
     Post => (A = A_2D_Arr'Update ((5, 7) | (X, Y) => V1));

   --  Update of two-dimensional array constant, choice list, possible
   --  overlap. Postcondition valid.

   procedure P7 (A  : out A3;
                 X1, X2  : in I;
                 Y1, Y2  : in M;
                 Z1, Z2  : in E;
                 V1 : in Integer;
                 V2 : in Integer)
     with Post => (if 1 = X2 and 2 = Y2 and Blue = Z2 then
     A = A_3D_Arr'Update ((1, 2, Blue) | (X1, Y1, Z1) => V1,
                          (X2, Y2, Z2) => V2));

   --  Same as above, but postcondition falsifiable.

   procedure P7_False (A  : out A3;
                       X1, X2  : in I;
                       Y1, Y2  : in M;
                       Z1, Z2  : in E;
                       V1 : in Integer;
                       V2 : in Integer)
     with Post => (if 2 = Y2 and Blue = Z2 then
     A = A_3D_Arr'Update ((1, 2, Blue) | (X1, Y1, Z1) => V1,
                          (X2, Y2, Z2) => V2));

end Update_Logic_Fn;
