with SM_Operations; use SM_Operations;

package body SM_Using_Table is

   type Transition_Record_T is
      record
         Initial_State : States_T;
         Trigger       : Triggers_T;
         New_State     : States_T;
         Op_Ptr        : Op_Ptr_T;
      end record;

   -- Calculate the array length based on the product of the number of states
   -- and number of transitions.
   --   Try changing the size to see what error message appears.
   Transition_Array_Size : constant :=
     ((States_T'Pos(States_T'Last) - States_T'Pos(States_T'First)) + 1) *
     ((Triggers_T'Pos(Triggers_T'Last) - Triggers_T'Pos(Triggers_T'First)) + 1);

   type Transition_Array_T is array(1 .. Transition_Array_Size) of
     Transition_Record_T;

   Transition_Array : constant Transition_Array_T := Transition_Array_T'(
     1 => Transition_Record_T'(Start,    Btn_Pressed,  Progress, SM_Operations.Null_Op_Ptr),
     2 => Transition_Record_T'(Start,    Btn_Released, Start,    SM_Operations.Null_Op_Ptr),
     3 => Transition_Record_T'(Progress, Btn_Pressed,  Finish,   SM_Operations.Null_Op_Ptr),
     4 => Transition_Record_T'(Progress, Btn_Released, Progress, SM_Operations.Null_Op_Ptr),
     5 => Transition_Record_T'(Finish,   Btn_Pressed,  Finish,   SM_Operations.Null_Op_Ptr),
     6 => Transition_Record_T'(Finish,   Btn_Released, Finish,   SM_Operations.Null_Op_Ptr));

   -- This assert ensures all states and all transitions from those states are
   -- defined. Additionally, it checks that each state is reachable ie all states
   -- are represented in the "Next_State" field.
   pragma Assert(for all State in States_T =>
                   (for all Trigger in Triggers_T =>
                       (for some Idx in 1 .. Transition_Array'Last =>
                          (State = Transition_Array(Idx).Initial_State and
                             Trigger = Transition_Array(Idx).Trigger))) and
                 (for all State in States_T =>
                       (for some Idx in 1 .. Transition_Array'Last =>
                          (State = Transition_Array(Idx).New_State))));

   State : States_T;

   procedure Initialise is
   begin
      State := States_T'First;
   end Initialise;

   procedure Progress_SM(Trigger : in Triggers_T) is
   begin
      -- This assert ensures all states and all transitions from those states are
      -- defined. Additionally, it checks that each state is reachable ie all states
      -- are represented in the "Next_State" field.
      pragma Assert (for all State in States_T =>
                      (for all Trigger in Triggers_T =>
                         (for some Idx in 1 .. Transition_Array'Last =>
                            (State = Transition_Array(Idx).Initial_State and
                               Trigger = Transition_Array(Idx).Trigger))) and
                      (for all State in States_T =>
                         (for some Idx in 1 .. Transition_Array'Last =>
                            (State = Transition_Array(Idx).New_State))));

      for I in Transition_Array'Range loop
         if Transition_Array(I).Initial_State = State then
            if Transition_Array(I).Trigger = Trigger then

               State := Transition_Array(I).New_State;
               SM_Operations.Execute_Op(Transition_Array(I).Op_Ptr, Trigger);

            end if;
         end if;
      end loop;
   end Progress_SM;

   function Is_Final_State return Boolean is
   begin
      return State = States_T'Last;
   end Is_Final_State;

end SM_Using_Table;
