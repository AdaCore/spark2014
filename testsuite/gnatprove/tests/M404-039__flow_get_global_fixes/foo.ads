package Foo
  with Abstract_State => State
is

  function Read_X return Integer
    with Global => State;

  function Read_Y return integer
    with Global => State;

  function Wibble return Boolean
    is (Read_X = 0)
    with Global => State;

end Foo;
