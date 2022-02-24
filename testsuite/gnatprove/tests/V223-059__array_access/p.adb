package body P with SPARK_Mode => on is
    function f(M : access T) return access Integer is
    begin
        return M.all(0);
    end f;
end P;
