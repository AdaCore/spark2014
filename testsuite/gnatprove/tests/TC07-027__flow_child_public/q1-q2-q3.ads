private package Q1.Q2.Q3 is
   pragma Elaborate_Body;
   X3A : Boolean with Part_Of => Q1.Q2.S2;
   X3B : Boolean with Part_Of => Q1.Q2.S2;
   X3C : Boolean := True with Part_Of => Q1.Q2.S2;
end;
