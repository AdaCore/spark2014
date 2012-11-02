package Swap_Add_14
with
   Abstract_State => (X, Y)
is

   procedure Swap
   with 
      Global  => (In_Out => (X, Y)),
      Depends => (X => Y,
	          Y => X);
   
   function Add return Integer
   with
      Global  => (Input => (X, Y));
   
end Swap_Add_14;
