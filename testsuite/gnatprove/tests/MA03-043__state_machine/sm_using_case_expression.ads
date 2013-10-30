with SM_Types; use SM_Types;

package SM_Using_Case_Expression
with SPARK_Mode,
     Abstract_State => Abs_State
is

   -- I have used state abstraction to demonstrate how the actual
   -- concrete definition of the state machine does not need to be visible
   -- in the package specification. To support this abstraction, I've
   -- added two functions to get and set the state.
   function Get_State return States_T
   with Global => Abs_State;

   procedure Set_State (New_State : in States_T)
   with Global => (Output => Abs_State),
        Post => Get_State = New_State;

   -- The following types set up an array or records where each record
   -- represents and invalid transition pair.
   type Invalid_Transition_Record_T is
      record
         Initial_State : States_T;
         Trigger       : Triggers_T;
      end record;

   -- Calculate the array length based on the product of the number of states
   -- and number of transitions.
   Invalid_Transition_Array_Size : constant :=
     ((States_T'Pos(States_T'Last) - States_T'Pos(States_T'First)) + 1) *
     ((Triggers_T'Pos(Triggers_T'Last) - Triggers_T'Pos(Triggers_T'First)) + 1);

   type Invalid_Transition_Array_T is array(1 .. Invalid_Transition_Array_Size) of
     Invalid_Transition_Record_T;

   -- This array defines all of the invalid transitions. This array is used
   -- to check that all valid transitions are defined.
   Invalid_Transition_Array : constant
     Invalid_Transition_Array_T := Invalid_Transition_Array_T'(
        1 => Invalid_Transition_Record_T'(Start,    Invalid_Trigger),
        --# Error Seed #3, comment out the next error
        2 => Invalid_Transition_Record_T'(Progress, Invalid_Trigger),
        3 => Invalid_Transition_Record_T'(Finish,   Invalid_Trigger),
        4 => Invalid_Transition_Record_T'(Invalid_State,   Btn_Pressed),
        5 => Invalid_Transition_Record_T'(Invalid_State,   Btn_Released),
        6 => Invalid_Transition_Record_T'(Invalid_State,   Btn_Start),
        7 => Invalid_Transition_Record_T'(Invalid_State,   Btn_Finish),
        8 => Invalid_Transition_Record_T'(Invalid_State,   Invalid_Trigger),
        Others => (Invalid_State, Invalid_Trigger));


   -- Initialises the system state to "Start"
   procedure Initialise
     with Global => (Output => Abs_State),
          Post => (Get_State = States_T'First);

   -- Expression function to specify the state machine
   function My_SM(State : in States_T; Trigger: in Triggers_T)
                  return States_T is
     (case State is
         -- Error Seed #2
         -- Replace all state updates to "Start" with "Finish"
         when Start =>
         (if    Trigger = Btn_Start    then Start
          elsif Trigger = Btn_Finish   then Finish
          elsif Trigger = Btn_Pressed  then Progress
          elsif Trigger = Btn_Released then Start
          else                              Invalid_State),
         when Progress =>
         (if    Trigger = Btn_Start    then Start
          elsif Trigger = Btn_Finish   then Finish
          elsif Trigger = Btn_Pressed  then Finish
          elsif Trigger = Btn_Released then Progress
          else                              Invalid_State),
         when Finish =>
         (if    Trigger = Btn_Start    then Start
          elsif Trigger = Btn_Finish   then Finish
          elsif Trigger = Btn_Pressed  then Finish
          elsif Trigger = Btn_Released then Finish
          else                              Invalid_State),
         when Invalid_State =>
         (if    Trigger = Btn_Start    then Start
          elsif Trigger = Btn_Finish   then Finish
          else                              Invalid_State));


   -- Progresses the system state based on the trigger
   procedure Progress_SM(Trigger : in Triggers_T)
   with Global => (In_Out => Abs_State),
        Post   => (Get_State = My_SM(Get_State'old, Trigger));


   -- Returns true if the state of the system is "Finish"
   function Is_Final_State return Boolean is (Get_State = States_T'Last) with
     Global => Abs_State;

end SM_Using_Case_Expression;
