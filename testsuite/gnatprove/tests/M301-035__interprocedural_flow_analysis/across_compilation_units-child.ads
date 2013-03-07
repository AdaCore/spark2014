package Across_Compilation_Units.Child is
   X, Y, Z: Integer;

   procedure Round_Swap_With_Depends_1
      with Global  => (In_Out => (X, Y, Z)),
           Depends => (X => Z,
                       Y => X,
                       Z => Y);

   procedure Round_Swap_With_Depends_2
      with Global  => (In_Out => (X, Y, Z)),
           Depends => (X => Z,
                       Y => X,
                       Z => Y);
end Across_Compilation_Units.Child;
