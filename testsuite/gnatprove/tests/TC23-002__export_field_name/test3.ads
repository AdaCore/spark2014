package Test3 with SPARK_Mode is

    type MyRecord is record
        reqDataLen : Integer;
        pragma Export (C, ReqDataLen, "reqDataLen");
        resDataLen : Integer;
        pragma Export (C, ResDataLen, "resDataLen");
    end record;
    pragma Export (C, MyRecord, "MyRecord");

    procedure func1(param : out MyRecord);

end Test3;
