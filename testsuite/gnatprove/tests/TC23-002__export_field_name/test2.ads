package test2 with SPARK_Mode is

    type MyRecord is record
        reqDataLen : Integer with Export, External_Name => "reqDataLen";
        resDataLen : Integer with Export, External_Name => "resDataLen";
    end record with Export, External_Name => "MyRecord";

    procedure func1(param : out MyRecord);

end test2;
