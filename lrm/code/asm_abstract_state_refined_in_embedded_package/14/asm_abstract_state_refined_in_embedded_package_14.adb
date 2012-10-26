
package body Power
with
   Refined_State => (State => (Source_A.State, Source_B.State));
is

  --  Embedded package spec for Source_A
  package Source_A
  with
     Abstract_State => State;
  is
     procedure Read (Level : out Integer);
     with
       Global  => State,
       Depends => (Level => State);
  end Source_A;

  --  Embedded package spec for Source_B.
  package Source_B
  with
     Abstract_State => State;
  is
    procedure Read (Level : out Integer);
    with
      Global  => State,
      Depends => (Level => State);
  end Source_B;

  --  Embedded package body for Source_A
  package body Source_A
  is
    State : Integer;

    procedure Read (Level : out Integer)
    is
    begin
      Level := State;
    end Read;
  end Source_A;

  --  Embedded package body for Source_B
  package body Source_B
  is
    State : Integer;

    procedure Read (Level : out Integer)
    is
    begin
      Level := State;
    end Read;

  end Source_B;

  procedure Read_Power(Level : out Integer)
  with
     Global => (Source_A.State, Source_B.State),
     Depends => (Level => (Source_A.State, Source_B.State));
  is
     Level_A : Integer;
     Level_B : Integer;
  begin
     Source_A. Read (Level_A);
     Source_B.Read (Level_B);
     Level := Level_A + Level_B;
  end Read_Power;

end Power;
