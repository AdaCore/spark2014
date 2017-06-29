private package Global_Contracts.State with
  SPARK_Mode
is
   B1 : Boolean with Part_Of => S1;
   B2 : Boolean with Part_Of => S1;
   G  : Integer with Part_Of => S2;
end Global_Contracts.State;
