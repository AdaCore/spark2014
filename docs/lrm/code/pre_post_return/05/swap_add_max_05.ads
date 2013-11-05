package Swap_Add_Max_05 is

   subtype Index      is Integer range 1..100;
   type    Array_Type is array (Index) of Integer;

   procedure Swap (X , Y : in out Integer);
   --# post X = Y~ and Y = X~;

   function Add (X, Y : Integer) return Integer;
   --# pre X + Y <= Integer'Last and X + Y >= Integer'First;
   --# return X + Y;

   function Max (X, Y : Integer) return Integer;
   --# return Z => (X >= Y -> Z = X) and
   --#             (Y >  X -> Z = Y);

   function Divide (X , Y : Integer) return Integer;
   --# pre Y /= 0 and X / Y <= Integer'Last;
   --# return X / Y;

   procedure Swap_Array_Elements(I, J : Index; A: in out Array_Type);
   --# post A = A~[I => A~(J); J => A~(I)];

end Swap_Add_Max_05;
