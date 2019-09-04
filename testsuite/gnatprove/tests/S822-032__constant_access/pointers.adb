package body Pointers with SPARK_Mode is

    function Read_X return Integer is
    begin
       return X.all;
    end Read_X;

    procedure Change_X is
    begin
       X.all := 1;
    end Change_X;

    procedure Change2_X is
    begin
       X.all := 1;
    end Change2_X;

end Pointers;
