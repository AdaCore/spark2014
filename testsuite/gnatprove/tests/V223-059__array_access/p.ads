package P with SPARK_Mode => on is
    type T is private;
    function f(M : access T)
    return access Integer;
private
    type T is array(0 .. 5) of access Integer;
end P;
