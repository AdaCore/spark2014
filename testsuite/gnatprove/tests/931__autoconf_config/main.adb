procedure Main is

  function Has_Check (X : Integer) return Integer is (X + 1) with Pre => True;
begin
  null;
end Main;
