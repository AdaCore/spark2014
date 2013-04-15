package Across_Compilation_Units.Child is
   --  Procedures Round_Swap_1, Round_Swap_2,
   --  Round_Swap_With_Depends_1 and
   --  Round_Swap_With_Depends_2 use procedures
   --  Swap and Swap_With_Depends of their parent
   --  package Across_Compilation_Units in order
   --  to perform a round swap of 3 global integers (X, Y, Z).

   --  This test illustrates 4 different cases:
   --    1) A procedure without contracts (Round_Swap_1) calls
   --       another procedure without contracts (Swap).
   --    2) A procedure without contracts (Round_Swap_2) calls
   --       a procedure with contracts (Swap_With_Depends).
   --    3) A procedure with contracts (Round_Swap_With_Depends_1)
   --       calls a procedure without contracts (Swap).
   --    4) A procedure with contracts (Round_Swap_With_Depends_2)
   --       calls a procedure without contracts (Swap_With_Depends).

   X, Y, Z: Integer;

   procedure Round_Swap_1;

   procedure Round_Swap_2;

   procedure Round_Swap_With_Depends_1
      with Global  => (In_Out => (X, Y, Z)),
           Depends => (X => Z,   --  This will raise a "'X' depends on 'X'" flow error
                                 --  and a "'X' depends on 'Y'" flow error.
                       Y => X,   --  This will raise a "'Y' depends on 'Y'" flow error
                       Z => Y);  --  This will raise a "'Z' depends on 'Z'" flow error
                                 --  and a "'Z' depends on 'X'" flow error.
   --  The previous errors are expected. The contracts on Round_Swap_With_Depends_1
   --  are technically correct but due to the fact that the called procedure Swap
   --  has computed derives (which are an overestimation of the real derives) this
   --  depends annotation should have been:
   --      Depends => (X =>+ (Z, Y),
   --                  Y =>+ X,
   --                  Z =>+ (Y, X))

   procedure Round_Swap_With_Depends_2
      with Global  => (In_Out => (X, Y, Z)),
           Depends => (X => Z,
                       Y => X,
                       Z => Y);
end Across_Compilation_Units.Child;
