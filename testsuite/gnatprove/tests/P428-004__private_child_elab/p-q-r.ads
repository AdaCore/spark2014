with P.Q; pragma Elaborate_All (P.Q);
private package P.Q.R is
   Y : Boolean := P.Q.X with Part_Of => P.Q.State;
   pragma Assert (P.Q.X);
end P.Q.R;
