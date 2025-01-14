procedure Pedantic is

  type X is (A, B, C);

  function To_String (A : X) return String with Pre => True is
  begin
    return X'Image (A);
  end To_String;
begin
  null;
end Pedantic;
