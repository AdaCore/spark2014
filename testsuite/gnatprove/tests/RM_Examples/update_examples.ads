package Update_Examples
  with SPARK_Mode
is
   type Rec is record
      X, Y : Integer;
   end record;

   type Arr is array (1 .. 3) of Integer;

   type Nested_Rec is record
      A : Integer;
      B : Rec;
      C : Arr;
   end record;

   type Nested_Arr is array (1 .. 3) of Nested_Rec;

   -- Simple record update
   procedure P1 (R : in out Rec)
     with Post => R = (R'Old with delta X => 1);
   -- this is equivalent to:
   --   R = (X => 1,
   --        Y => R'Old.Y)

   -- Simple 1D array update
   procedure P2 (A : in out Arr)
     with Post => A = (A'Old with delta 1 => 2);
   -- this is equivalent to:
   --   A = (1 => 2,
   --        2 => A'Old (2),
   --        3 => A'Old (3));

   -- Nested record update
   procedure P3 (NR : in out Nested_Rec)
     with Post => NR = (NR'Old with delta A => 1,
                                          B => (NR'Old.B with delta X => 1),
                                          C => (NR'Old.C with delta 1 => 5));
   -- this is equivalent to:
   --   NR = (A => 1,
   --         B.X => 1,
   --         B.Y => NR'Old.B.Y,
   --         C (1) => 5,
   --         C (2) => NR'Old.C (2),
   --         C (3) => NR'Old.C (3))

   -- Nested array update
   procedure P4 (NA : in out Nested_Arr)
     with Post =>
       NA = (NA'Old with delta
               1 => (NA'Old (1) with delta A => 1),
               2 => (NA'Old (2) with delta
                       B => (NA'Old (2).B with delta X => 2)),
               3 => (NA'Old (3) with delta
                       C => (NA'Old (3).C with delta 1 => 5)));
   -- this is equivalent to:
   --   NA = (1 => (A => 1,
   --               B => NA'Old (1).B,
   --               C => NA'Old (1).C),
   --         2 => (B.X => 2,
   --               B.Y => NA'Old (2).B.Y,
   --               A => NA'Old (2).A,
   --               C => NA'Old (2).C),
   --         3 => (C => (1 => 5,
   --                     2 => NA'Old (3).C (2),
   --                     3 => NA'Old (3).C (3)),
   --               A => NA'Old (3).A,
   --               B => NA'Old (3).B));

end Update_Examples;
