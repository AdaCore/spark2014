package SS_Default is

    task type TT;

    function SS return Integer is (TT'Storage_Size);

    pragma Assert (TT'Storage_Size >= 0);

end;
