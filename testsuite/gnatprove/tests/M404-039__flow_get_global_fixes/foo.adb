package body Foo
  with Refined_State => (State => (X, Y))
is

  X : Integer;
  Y : Integer;

  function Read_X return Integer
  with Refined_Global => X
  is
  begin
     return X;
  end Read_X;

  function Read_Y return Integer is (Y)
  with Refined_Global => Y;

  procedure Test_01
    with Global => (Input => Y,
                    In_Out => X)
  is
  begin
     if Wibble then
        X := 12;
     end if;
  end Test_01;

end Foo;
