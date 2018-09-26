package P with Abstract_State => (State1, State2, State3) is
   procedure Proc1
     with Global => State1;

   procedure Proc2
     with Depends => (State1 => null);

   procedure Proc3
     with Global => (State3);

   procedure Proc4
     with Depends => (State3 => State3);

   procedure Proc5
     with Global  => (In_Out => State1),
          Depends => (State1 => State1);

   procedure Proc6
     with Global  => (In_Out => State1),
          Depends => (State1 => State1);
end P;
