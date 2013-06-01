pragma Ada_2012;
procedure P is
    X : constant String(5..7) := (5 => 'a', 6 => 'b', 7 => 'c');
    subtype Str3 is String(1..3);
    function Blah(S : Str3) return Boolean is (S(1) = 'a');
begin
    pragma Assert(Blah(X));  -- Sliding changes indices to be 1..3
end P;
