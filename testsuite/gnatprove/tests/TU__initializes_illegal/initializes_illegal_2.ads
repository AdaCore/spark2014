package Initializes_Illegal_2
  --  TU: 2. The Initializes aspect shall follow the Abstract_State aspect if
  --  one is present.
  with SPARK_Mode,
       Initializes    => (S, X),
       Abstract_State => S
is
   X : Integer;
end Initializes_Illegal_2;
