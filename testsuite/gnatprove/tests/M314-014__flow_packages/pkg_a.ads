package Pkg_A
  with Abstract_State => (State_A, State_B),
       Initializes    => (State_A, X, Z, Q)
is
   pragma Elaborate_Body (Pkg_A);


   X : Integer;           --  error: not initialized
   Y : Integer;
   Z : Integer := 12345;  --  "I have the same combination on my suitcase"
                          --  error: ineffective due to body init
   W : Integer;
   Q : Integer;

end Pkg_A;
