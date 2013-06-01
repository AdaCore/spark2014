package Vehicle is

   type State_Type is (Still, Forward, Backward);

   type Input is (No_Input, Nothing, Accelerate, Brake);

   subtype Valid_Input is Input range Nothing .. Brake;

   Max_Speed : constant := 100;

   type Speed_Type is range -Max_Speed .. Max_Speed;

   Speed : Speed_Type;
   State : State_Type;

   function Speed_Is_Valid return Boolean is
      (case State is
         when Still    => Speed = 0,
         when Forward  => Speed > 0,
         when Backward => Speed < 0);

   procedure State_Update (I : Valid_Input)
      with Pre => Speed_Is_Valid,
           Post => Speed_Is_Valid,
           Global => (In_Out => (State, Speed));

   type Reader is access function return Input;

   procedure Execute (Read : Reader)
      with Pre => Speed_Is_Valid,
           Post => State = Still and Speed_Is_Valid,
           Test_Case =>
             (Name     => "Segway standing still",
              Mode     => Nominal,
              Requires => State = Still),
           Test_Case =>
             (Name     => "Segway moving forward",
              Mode     => Nominal,
              Requires => State = Forward),
           Test_Case =>
             (Name     => "Segway moving backward",
              Mode     => Nominal,
              Requires => State = Backward);

end Vehicle;
