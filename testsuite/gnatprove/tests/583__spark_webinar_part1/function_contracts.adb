package body Function_Contracts
    with SPARK_Mode
is
    -- Basic functional contract

    function Maximum (X, Y : Integer) return Integer is
        (Integer'Max (X, X));

    procedure Swap (X, Y : in out Integer) is
        Tmp : constant Integer := X;
    begin
        X := Tmp;
        Y := Tmp;
    end Swap;

    -- Exceptions and termination

    procedure May_Raise (Arg : Integer) is
    begin
        if Arg /= 0 then
            raise Constraint_Error;
        end if;
    end May_Raise;

    procedure May_Halt (Arg : Integer) is
    begin
        if Arg >= 0 then
            while True loop
                null;
            end loop;
        end if;
    end May_Halt;

end Function_Contracts;
