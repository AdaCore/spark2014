package body Power_14
   with Refined_State => (State => (Source_A.State, Source_B.State))
is

  --  Embedded package spec for Source_A
  package Source_A
     with Abstract_State => State
  is
     procedure Read (Level : out Integer)
        with Global  => State,
             Depends => (Level => State);
  end Source_A;

  --  Embedded package spec for Source_B.
  package Source_B
  with
     Abstract_State => State
  is
    procedure Read (Level : out Integer)
       with Global  => State,
            Depends => (Level => State);
  end Source_B;

  --  Embedded package body for Source_A
  package body Source_A
     with Refined_State => (State => S)
  is
    S : Integer;

    procedure Read (Level : out Integer)
       with Refined_Global  => S,
            Refined_Depends => (Level => S)
    is
    begin
      Level := S;
    end Read;
  end Source_A;

  --  Embedded package body for Source_B
  package body Source_B
     with Refined_State => (State => S)
  is
    S : Integer;

    procedure Read (Level : out Integer)
       with Refined_Global  => S,
            Refined_Depends => (Level => S)
    is
    begin
      Level := S;
    end Read;

  end Source_B;

  procedure Read_Power(Level : out Integer)
     with Refined_Global  => (Source_A.State, Source_B.State),
          Refined_Depends => (Level => (Source_A.State, Source_B.State))
  is
     Level_A : Integer;
     Level_B : Integer;
  begin
     Source_A. Read (Level_A);
     Source_B.Read (Level_B);
     Level := Level_A + Level_B;
  end Read_Power;

end Power_14;
