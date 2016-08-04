package Segway is

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
        Post => Speed_Is_Valid;

   procedure Halt
   with Pre  => Speed_Is_Valid,
        Post => State = Still and Speed_Is_Valid;

end Segway;
