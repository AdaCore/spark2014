package Early_Init
is
   package Inner_1
   with Initializes => V1,
        Initial_Condition => V1 <= 100
   is
      V1 : Positive;
      function F1 (X : Positive) return Positive;
   end Inner_1;


   package Inner_2
   with Initializes => (V2 => Inner_1.V1),
        Initial_Condition => V2 = Inner_1.V1
   is
      V2 : Positive := Inner_1.V1;
      function F2 (Y : Positive) return Positive;
   end Inner_2;

end Early_Init;
