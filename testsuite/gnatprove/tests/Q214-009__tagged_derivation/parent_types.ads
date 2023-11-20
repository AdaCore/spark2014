package Parent_Types with SPARK_Mode is
    type T is private;
    function Valid (X : T) return Boolean is (True) with
     Post => Valid'Result;

private
    type T is tagged record
       C : Integer := 0;
    end record;
end Parent_Types;
