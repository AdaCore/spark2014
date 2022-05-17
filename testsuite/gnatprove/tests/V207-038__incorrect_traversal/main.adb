procedure Main with SPARK_Mode is
    type t1 is record
        null;
    end record;
    type t2 is access t1;
    type t3 is array (Natural range <>) of t2;
    type t4 is record
        t2_inst : t2;
    end record;
    function f(i : in Integer) return access t4 is
    begin
        return null;
    end f;
    t3_inst : t3(0 .. 2) := (others => null);
begin
    t3_inst(0) := f(1).all.t2_inst;
end;
