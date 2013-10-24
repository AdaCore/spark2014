package Update is

   pragma SPARK_Mode (On);

   type Index is range 1 .. 8;

   type Array_1D is array (Index) of Integer;
   type Array_2D is array (Index, Index) of Integer;

   type Array_3D is array (Natural range 1 .. 5,
                           Natural range 1 .. 5,
                           Natural range 1 .. 5) of Integer;

   X : Integer;
   An_Arr : Array_1D := Array_1D'(others => 7);

   ----------------------------------------------------------------------------
   -- 'Update Array tests
   ----------------------------------------------------------------------------

   --  aggregate reference test, compare WHY VC models
   function F1 (Init_Val : Integer) return Array_1D
     with Pre => Init_Val < Integer'Last,
          Post => (F1'Result =
                     Array_1D'(1..2   => X,
                               3      => Init_Val + 1,
                               Others => An_Arr(5)));

   --  basic array update, loop reference test
   procedure Basic_Array_Update (A: in out Array_1D;
                                 I: in Index;
                                 New_Val: in Integer)
     with Post => (for all J in Index =>
                     (if I /= J then A(J) = A'Old(J) else A(J) = New_Val));

   --  same basic array test using 'Update, one dynamic choice,
   --  prefix is in/out parameter
   procedure Basic_Array_Update2 (A: in out Array_1D;
                                  I: in Index;
                                  New_Val: in Integer)
     with Post => A = A'Old'Update(I => New_Val);

   --  dynamic choice interval
   function F2 (Arr_In : Array_1D; I : Index) return Array_1D
     with Post => (F2'Result = Arr_In'Update(1..I => 7));

   --  overlapping choice intervals
   function F3 (Arr_In : Array_1D) return Array_1D
     with Post => (F3'Result = Arr_In'Update(1..4 => X,
                                             2    => 1,
                                             3    => An_Arr(4)));

   --  several dynamic choices, overlapping intervals
   function F4 (Arr_In : Array_1D; I : Index; J : Index) return Array_1D
     with Post => (F4'Result = Arr_In'Update(1..I => 10, I..J => 20));

   --  single association (special case in gnat2why code)
   function F5 (Arr_In : Array_1D) return Array_1D
     with Post => (F5'Result = Arr_In'Update(2 => 1));

   --  prefix is aggregate
   procedure My_Init_Array (A: out Array_1D)
     with Post => A = Array_1D'(others => 1)'Update(3 => 2, 4..5 => 3);

   --  prefix is aggregate, dynamic choice
   procedure My_Init_Array2 (A: out Array_1D; I : in Index)
     with Post => A = Array_1D'(others => 1)'Update(I => 2, 4..5 => X);

   --  prefix is 'Old attribute
   procedure Swap_Elements (I, J: in Index; A: in out Array_1D)
     with Post => (A = A'Old'Update(I => A'Old(J), J => A'Old(I)));

   --  array update, swap inversion check, prefix is 'Result
   function Swap_Fun (Arr_In : Array_1D; I, J : Index) return Array_1D
     with Post => (Swap_Fun'Result'Update(I => Swap_Fun'Result(J),
                                          J => Swap_Fun'Result(I)) = Arr_In);

end Update;
