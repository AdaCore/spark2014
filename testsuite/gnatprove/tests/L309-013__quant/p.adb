procedure P is
    function F (X : Integer) return Boolean is (X > 5);
    type Barr is array (1 .. 10) of Boolean;
    B : Barr;
begin
    B := (others => (for some J in 1 .. 10 => F (J)));
end P;
