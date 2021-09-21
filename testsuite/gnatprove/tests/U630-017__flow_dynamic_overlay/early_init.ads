package Early_Init is

   procedure Dummy;

   package Inner_1
   with Initializes => V1,
        Initial_Condition => V1 <= 100
   is
      V1 : Positive with Alignment => 4;
      V2 : Positive := 1 with Address => V1'Address, Alignment => 4;
   end Inner_1;

end Early_Init;
