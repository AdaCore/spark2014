package body Exceptions with
    SPARK_Mode => Off
is

    -- We supply implementations for the Ghost functions in case ghost code is enabled. Our
    -- implementation is not thread-safe, however.

    Internal_Thrown : Boolean := False;
    Pragma Volatile(Internal_Thrown);

    Internal_Cause : Cause_Type;
    Pragma Volatile(Internal_Cause);

    function Is_Thrown return Boolean is (Internal_Thrown);

    function Get_Cause return Cause_Type is (Internal_Cause);

    procedure Throw(Cause : Cause_Type) is
    begin
        Internal_Cause := Cause;
        Internal_Thrown := True;
        Report_Exception(Cause);
    end Throw;

end Exceptions;
