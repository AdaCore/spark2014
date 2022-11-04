procedure Main
with
    SPARK_Mode => On
is
    type R_1 is record
        i : Natural := 0;
        j : Natural := 0;
    end record;
    type R_1_array is array (Natural range<>) of R_1;
    type R_2(N : Natural) is record
        a : R_1_array(1 .. N);
        b : Boolean := True;
    end record
    with
        Dynamic_predicate => (if b then
            (for all x of R_2.a => x.i = 0));
    procedure p(r : in out R_1) with
      Global => null
    is
    begin
        r.i := 1;
    end p;
    y : R_2(3);
begin
    if y.b then
        pragma Assert(for all x of y.a => x.i = 0);
        p(y.a(1));
    end if;
end Main;
