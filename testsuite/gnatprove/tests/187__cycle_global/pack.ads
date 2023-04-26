package Pack
    with SPARK_Mode => on
is
    type Enum is (A, B);
    type Int_Arr is array (Enum) of Integer;

    Glob : constant Int_Arr := (A => 1, B => 2);

    function H (X : Integer) return Boolean is (X * 2 = Glob(A));

    function G (X : Integer) return Boolean is (H (X));

    type IntArr is array (Natural range <>) of Integer;

    type MyRec (MaxSlot : Natural)
        is record
        F1 : IntArr (Natural'First .. MaxSlot) := (others => 1);
        F2 : Integer := 0;
    end record
    with Dynamic_Predicate => (if MyRec.F2 = 1 then (G (MyRec.F1(MyRec.F1'First))));

end Pack;
