package Types with SPARK_Mode is
    type T is private;
    function Valid (X : T) return Boolean is (True) with
     Post => Valid'Result;

    type P is private;

    function Valid (X : P) return Boolean with
     Post => Valid'Result;

private
    type T is tagged record
       C : Integer := 0;
    end record;

    type R is new T with null record;

    function Valid (X : R) return Boolean is (False) with
     Post'Class => not Valid'Result;

    type P is new R with null record;

    function Valid (X : P) return Boolean is (True);
end Types;
