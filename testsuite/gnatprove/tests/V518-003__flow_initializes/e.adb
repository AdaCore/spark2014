package body E with
    SPARK_Mode => Off
is
    -- Supply implementations for the Ghost functions in case ghost code is enabled

    Internal_Thrown : Boolean := False;
    Pragma Volatile(Internal_Thrown);

    function Is_Thrown return Boolean is (Internal_Thrown);

end E;
