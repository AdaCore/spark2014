pragma SPARK_Mode (On);

package Segway is

   type State_Type is (Still, Forward, Backward);

   type Input is (No_Input, Nothing, Accelerate, Brake);

   subtype Valid_Input is Input range Nothing .. Brake;

   Max_Speed : constant := 100;

   type Speed_Type is range -Max_Speed .. Max_Speed;

   Speed : Speed_Type;
   State : State_Type;

   function Speed_Is_Valid return Boolean
   is
      (case State is
         when Still    => Speed = 0,
         when Forward  => Speed > 0,
         when Backward => Speed < 0)
     with Global => (Speed, State);

   procedure State_Update (I : Valid_Input)
   with Global => (In_Out => (State, Speed)),
        Depends => ((State, Speed) =>+ (Speed, I)),
        Pre => Speed_Is_Valid,
        Post => Speed_Is_Valid;

   procedure Halt
   with Global => (In_Out => (State, Speed)),
        Depends => ((State, Speed) => (State, Speed)),
        Pre  => Speed_Is_Valid,
        Post => State = Still and Speed_Is_Valid;

end Segway;
