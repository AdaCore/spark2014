with sPIN;

pragma Elaborate (sPIN);

procedure sPIN_Main
is
   State : sPIN.State_Type;
begin

   sPIN.Initialize (State);
   loop
      pragma Loop_Invariant (sPIN.State_Invariant (State));
      sPIN.Display (State);
   end loop;

end sPIN_Main;
