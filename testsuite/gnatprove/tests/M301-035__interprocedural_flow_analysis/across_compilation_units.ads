package Across_Compilation_Units is
   function Prime (X: Natural) return Boolean;

   procedure Swap (X, Y: in out Integer);

   procedure Swap_With_Depends (X, Y: in out Integer)
      with Depends => (X => Y,
                       Y => X);
end Across_Compilation_Units;
