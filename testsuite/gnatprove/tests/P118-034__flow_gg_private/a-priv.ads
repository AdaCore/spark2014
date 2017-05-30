private package A.Priv is

   I : Integer with Part_Of => State_A;

   function F_5 return Integer is (I);

   function F_6 return Integer;

end A.Priv;
