package Segway
  with SPARK_Mode,
       Abstract_State => State
is

   type Status_Type is (Still, Forward, Backward);

   type Input is (No_Input, Nothing, Accelerate, Brake);

   subtype Valid_Input is Input range Nothing .. Brake;

   Max_Speed : constant := 100;

   type Speed_Type is range -Max_Speed .. Max_Speed;

   function Current_Status return Status_Type
     with Global => State;

   function Current_Speed return Speed_Type
     with Global => State;

   function Speed_Is_Valid return Boolean
   --  Expresses the required invariant relationship between
   --  Current_Speed and Current_Status
   is
      (case Current_Status is
         when Still    => Current_Speed = 0,
         when Forward  => Current_Speed > 0,
         when Backward => Current_Speed < 0)
     with Global => State;

   procedure Initialize
     with Global  => (Output => State),
          Depends => (State => null),
          Post    => Speed_Is_Valid and Current_Status = Still;
   --  Initializes State and establishes initial invariant

   procedure State_Update (I : Valid_Input)
     with Global  => (In_Out => State),
          Depends => (State => (State, I)),
          Pre     => Speed_Is_Valid,
          Post    => Speed_Is_Valid;

   procedure Halt
     with Global  => (In_Out => State),
          Depends => (State => State),
          Pre     => Speed_Is_Valid,
          Post    => Speed_Is_Valid and Current_Status = Still;

end Segway;
