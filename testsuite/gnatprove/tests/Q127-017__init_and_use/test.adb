package body test
  with Spark_Mode
is

    procedure user
    is
    begin
       A := B;
    end user;

    procedure init
    is
    begin
       B := 0;
    end init;

end test;
