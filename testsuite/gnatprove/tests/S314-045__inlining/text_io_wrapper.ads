package Text_IO_Wrapper with SPARK_Mode is
  procedure Put(S: String) with Global => null;
  procedure Put(I, N: Integer) with Global => null;
  procedure Put(C: Character) with Global => null;
  procedure New_Line(N: Integer) with Global => null;
  function Get_Line return String with Global => null;
  function End_Of_File return Boolean with Global => null;
end Text_IO_Wrapper;
