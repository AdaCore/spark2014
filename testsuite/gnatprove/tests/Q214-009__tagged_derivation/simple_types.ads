package Simple_Types with SPARK_Mode is
    type T is private;
private
    type T is tagged null record;
    type R is new T with null record;
end Simple_Types;
