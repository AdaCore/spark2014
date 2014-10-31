with Parent;
with Parent.Child_1;

procedure Scheduler
  with Global => (Output => (Parent.State,
                             Parent.Child_1.State))
is
   pragma SPARK_Mode;
begin

   Parent.Initialise;

end Scheduler;
