package Update_Examples
  with SPARK_Mode
is
   type Rec is record
      X, Y : Integer;
   end record;

   type Arr is array (1 .. 3) of Integer;

   type Arr_2D is array (1 .. 3, 1 .. 3) of Integer;

   type Nested_Rec is record
      A : Integer;
      B : Rec;
      C : Arr;
      D : Arr_2D;
   end record;

   type Nested_Arr is array (1 .. 3) of Nested_Rec;

   -- Simple record update
   procedure P1 (R : in out Rec)
     with Post => R = R'Old'Update (X => 1);
   -- this is equivalent to:
   --   R = (X => 1,
   --        Y => R'Old.Y)

   -- Simple 1D array update
   procedure P2 (A : in out Arr)
     with Post => A = A'Old'Update (1 => 2);
   -- this is equivalent to:
   --   A = (1 => 2,
   --        2 => A'Old (2),
   --        3 => A'Old (3));

   -- 2D array update
   procedure P3 (A2D : in out Arr_2D)
     with Post => A2D = A2D'Old'Update ((1, 1) => 1,
                                        (2, 2) => 2,
                                        (3, 3) => 3);
   -- this is equivalent to:
   --   A2D = (1 => (1 => 1,
   --                2 => A2D'Old (1, 2),
   --                3 => A2D'Old (1, 3)),
   --          2 => (2 => 2,
   --                1 => A2D'Old (2, 1),
   --                3 => A2D'Old (2, 3)),
   --          3 => (3 => 3,
   --                1 => A2D'Old (3, 1),
   --                2 => A2D'Old (3, 2)));

   -- Nested record update
   procedure P4 (NR : in out Nested_Rec)
     with Post => NR = NR'Old'Update (A => 1,
                                      B => NR'Old.B'Update (X => 1),
                                      C => NR'Old.C'Update (1 => 5));
   -- this is equivalent to:
   --   NR = (A => 1,
   --         B.X => 1,
   --         B.Y => NR'Old.B.Y,
   --         C (1) => 5,
   --         C (2) => NR'Old.C (2),
   --         C (3) => NR'Old.C (3),
   --         D => NR'Old.D)

   -- Nested array update
   procedure P5 (NA : in out Nested_Arr)
     with Post =>
       NA = NA'Old'Update (1 => NA'Old (1)'Update
                                  (A => 1,
                                   D => NA'Old (1).D'Update ((2, 2) => 0)),
                           2 => NA'Old (2)'Update
                                  (B => NA'Old (2).B'Update (X => 2)),
                           3 => NA'Old (3)'Update
                                  (C => NA'Old (3).C'Update (1 => 5)));
   -- this is equivalent to:
   --   NA = (1 => (A => 1,
   --               B => NA'Old (1).B,
   --               C => NA'Old (1).C,
   --               D => NA'Old (1).D),
   --         2 => (B.X => 2,
   --               B.Y => NA'Old (2).B.Y,
   --               A => NA'Old (2).A,
   --               C => NA'Old (2).C,
   --               D => NA'Old (2).D),
   --         3 => (C => (1 => 5,
   --                     2 => NA'Old (3).C (2),
   --                     3 => NA'Old (3).C (3)),
   --               A => NA'Old (3).A,
   --               B => NA'Old (3).B,
   --               D => NA'Old (3).D));

end Update_Examples;
