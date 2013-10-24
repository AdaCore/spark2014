package Swap_Add_Max_14
  with Abstract_State => (X, Y)
is
   subtype Index      is Integer range 1..100;
   type    Array_Type is array (Index) of Integer;

   procedure Swap
     with Global  => (In_Out => (X, Y)),
          Depends => (X => Y,
                      Y => X),
          Post    => (X = Y'Old and Y = X'Old);

   function Add return Integer
     with Global  => (Input => (X, Y)),
          Post    => Add'Result = X + Y;

   function Max return Integer
     with Global  => (Input => (X, Y)),
          Post    => (if X >= Y then Max'Result = X
                      else Max'Result = Y);

   function Divide return Float
     with Global  => (Input => (X, Y)),
          Pre     => Y /= 0,
          Post    => Divide'Result = Float(X / Y);

   procedure Swap_Array_Elements(A: in out Array_Type)
     with Global  => (Input => (X, Y)),
          Depends => (A => (A, X, Y)),
          Pre     => X in Index and Y in Index,
          Post    => A = A'Old'Update (X => A'Old (Y), Y => A'Old (X));
end Swap_Add_Max_14;
