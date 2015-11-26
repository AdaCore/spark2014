package SS_Defined is

    task type TT1 with Storage_Size => 1024;
    task type TT2;
    for TT2'Storage_Size use 1024;

    pragma Assert (TT1'Storage_Size = TT2'Storage_Size);

end;
