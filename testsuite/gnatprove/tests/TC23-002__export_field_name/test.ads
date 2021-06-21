package test with SPARK_Mode is

    type MyRecord is record
        reqDataLen : Integer;
        pragma External(C,reqDataLen,"reqDataLen");
        resDataLen : Integer;
        pragma External(C,resDataLen,"resDataLen");
    end record;
    pragma External(C,MyRecord,"MyRecord");

    procedure func1(param : out MyRecord);

end test;
