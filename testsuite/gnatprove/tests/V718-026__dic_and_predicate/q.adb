package body Q with SPARK_Mode is

    function Model return Set_Model is
       Result : Set_Model;
    begin
       pragma Assert (Is_Empty (Result));
       return Result;
    end Model;

end Q;
