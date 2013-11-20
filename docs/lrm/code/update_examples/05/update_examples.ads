package Update_Examples
is
   type Rec is record
      X, Y : Integer;
   end record;

   type Index is range 1 ..3;

   type Arr is array (Index) of Integer;

   type Arr_2D is array (Index, Index) of Integer;

   type Nested_Rec is record
      A : Integer;
      B : Rec;
      C : Arr;
      D : Arr_2D;
   end record;

   type Nested_Arr is array (Index) of Nested_Rec;

   -- Simple record update
   procedure P1 (R : in out Rec);
   --# post R = R~ [X => 1];

   -- Simple 1D array update
   procedure P2 (A : in out Arr);
   --# post A = A~ [1 => 2];

   -- 2D array update
   procedure P3 (A2D : in out Arr_2D);
   --# post A2D = A2D~ [1, 1 => 1;
   --#                  2, 2 => 2;
   --#                  3, 3 => 3];

   -- Nested record update
   procedure P4 (NR : in out Nested_Rec);
   --# post NR = NR~ [A => 1;
   --#                B => NR~.B [X => 1];
   --#                C => NR~.C [1 => 5]];

   -- Nested array update
   procedure P5 (NA : in out Nested_Arr);
   --# post NA = NA~ [1 => NA~ (1) [A => 1;
   --#                              D => NA~ (1).D [2, 2 => 0]];
   --#                2 => NA~ (2) [B => NA~ (2).B [X => 2]];
   --#                3 => NA~ (3) [C => NA~ (3).C [1 => 5]]];
end Update_Examples;
