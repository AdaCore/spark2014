package body State_Machine
  with SPARK_Mode
is

  Flag : Boolean;
  Num  : Integer;
  --  Defined states are
  --     (true, > 0)
  --     (true, <= 0)
  --     (false, > 0)
  --     (false, <= 0)
  --  Undefined state is
  --     (false, 0) because we will have a bug where (false, <= 0) is
  --     implemented using (false, < 0)

  function State_A return Boolean is (Flag and Num > 0);

  function State_B return Boolean is (Flag and Num <= 0);

  function State_C return Boolean is (not Flag and Num > 0);

  function State_D return Boolean is (not Flag and Num < 0);  --  bug is here

  procedure Do_Transition
  with Contract_Cases => (State_A => State_A,
                          State_B => State_A or State_B,
                          State_C => State_B,
                          State_D => State_C or State_D,
                          others  => False)
  is
  begin
     if State_A then
        --  do nothing, terminal state
        null;
     elsif State_B then
        Num := Num + 1;
     elsif State_C then
        Flag := True;
        Num  := - Num;
     elsif State_D then
        Num := Num + 1;
     else
        --  This can never happen. Or can it? :)
        pragma Assert (False);
     end if;
  end Do_Transition;

  --  procedure Foo
  --    with Contract_Cases => (Num > 0 => True,
  --                            Num <= 0 => True,
  --                            others => False)
  --    is
  --    begin
  --       null;
  --    end Foo;


end State_Machine;
