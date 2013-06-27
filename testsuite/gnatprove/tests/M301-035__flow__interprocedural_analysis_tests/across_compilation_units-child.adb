package body Across_Compilation_Units.Child is
   procedure Round_Swap_1 is
   begin
      Swap (X, Y);
      Swap (X, Z);
   end Round_Swap_1;

   procedure Round_Swap_2 is
   begin
      Swap_With_Depends (X, Y);
      Swap_With_Depends (X, Z);
   end Round_Swap_2;

   procedure Round_Swap_With_Depends_1 is
   begin
      Swap (X, Y);
      Swap (X, Z);
   end Round_Swap_With_Depends_1;

   procedure Round_Swap_With_Depends_2 is
   begin
      Swap_With_Depends (X, Y);
      Swap_With_Depends (X, Z);
   end Round_Swap_With_Depends_2;
end Across_Compilation_Units.Child;
