package Function_Contracts
    with SPARK_Mode
is
    -- Basic functional contract

    function Maximum (X, Y : Integer) return Integer
    with
        Pre => X /= Y,
        Post => (if X < Y then Maximum'Result = Y else Maximum'Result = X);

    procedure Swap (X, Y : in out Integer)
    with
        Global => null,
        Post => X = Y'Old and Y = X'Old;

    -- Exceptions and termination

    procedure May_Raise (Arg : Integer)
    with
        Exceptional_Cases => (Constraint_Error => Arg = 0);

    procedure May_Halt (Arg : Integer)
    with
        Always_Terminates => Arg /= 0;

end Function_Contracts;
