package P with SPARK_Mode => on is
    type T is private;
    function f(M : access T)
    return access Integer;
private
    type Integer_Acc is access Integer;
    type T is array(0 .. 5) of Integer_Acc;
end P;
