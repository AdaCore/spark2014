package Interfering_Volatile_Attribute is

    task T;

    function Check return Boolean is
       (T'Terminated);

end;
