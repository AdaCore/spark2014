private package P.Q is
   X : Boolean := True with Part_Of => P.State;
   procedure Dummy with Global => null;
end P.Q;
