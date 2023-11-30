package Parent_Types.Public_Child with SPARK_Mode is
    type P is private;

    function Valid (X : P) return Boolean with
     Post => Valid'Result;

private
    type R is new T with null record;

    function Valid (X : R) return Boolean is (False) with
     Post'Class => not Valid'Result;

    type P is new R with null record;

    function Valid (X : P) return Boolean is (True);
end Parent_Types.Public_Child;
