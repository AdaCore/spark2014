package Uninitialized is
   A : Integer;

   procedure Compare
      with Global => (Output => A);
end Uninitialized;
