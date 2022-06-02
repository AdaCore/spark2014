package body My_Lib with
    SPARK_Mode => On
is

    procedure Try_Cast(Input : Integer; Output : out Optional_Natural) is
    begin
        if Input >= 0 then
            Output := Optional_Natural'(Valid => True, Value => Natural(Input));
        else
            E.Throw(Cast_Error_Message);
            Output := No_Natural;
        end if;
    end Try_Cast;

end My_Lib;
