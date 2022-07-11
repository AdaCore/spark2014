package P with
  SPARK_Mode
is
   package Q with
     SPARK_Mode,
     Abstract_State => (S1, S2),
     Initializes => (S1, S2),
     Initial_Condition => Valid
   is
      function Valid return Boolean with Global => (S1, S2);
   end Q;
end P;
