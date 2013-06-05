package Swap_Add_14
   with Abstract_State => (X, Y)
is
   procedure Swap
      with Global  => (In_Out => (X, Y)),
           Depends => (X => Y,   -- to be read as "X depends on Y"
	               Y => X);  -- to be read as "Y depends on X"
   
   function Add return Integer
      with Global  => (Input => (X, Y));
end Swap_Add_14;
