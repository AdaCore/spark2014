package body Nuclear_Reactors with
  SPARK_Mode,
  Refined_State => (State => Cur_State)
is
   type Reactor_State is (Stopped, Working) with Atomic;

   Cur_State : Reactor_State
     with Async_Readers, Async_Writers, Atomic;

   procedure Shut_Down is
   begin
      Cur_State := Stopped;
   end Shut_Down;

   procedure Emergency_Stop is
   begin
      Cur_State := Stopped;
   end Emergency_Stop;

end Nuclear_Reactors;
