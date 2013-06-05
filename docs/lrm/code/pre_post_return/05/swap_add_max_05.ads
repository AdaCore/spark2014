package Swap_Add_Max_05
--# own X, Y: Integer;
is

   subtype Index      is Integer range 1..100;
   type    Array_Type is array (Index) of Integer;

   procedure Swap;
   --# global in out X, Y;
   --# derives X from Y &
   --#         Y from X;
   --# post X = Y~ and Y = X~;

   function Add return Integer;
   --# global in X, Y;
   --# return X + Y;

   function Max return Integer;
   --# global in X, Y;
   --# return Z => (X >= Y -> Z = X) and
   --#             (Y >  X -> Z = Y);

   function Divide return Float;
   --# global in X, Y;
   --# pre Y /= 0;
   --# return Float(X / Y);

   procedure Swap_Array_Elements(A: in out Array_Type);
   --# global in X, Y;
   --# derives A from A, X, Y;
   --# pre  X in Index and Y in Index;
   --# post A = A~[X => A~(Y); Y => A~(X)];

end Swap_Add_Max_05;
