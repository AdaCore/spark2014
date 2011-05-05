package Error is

   type State is (Erroneous, Normal);

   function Get_Current return State;

   procedure Set_Erroneous;

   procedure Reset;

private

   MyState : State := Normal;

end Error;
