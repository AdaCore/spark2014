package TTI is

    task T;

    function Terminated return Boolean is (T'Terminated) with Volatile_Function;

end;
