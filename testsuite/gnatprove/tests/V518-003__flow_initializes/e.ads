package E with
    SPARK_Mode => On,
    Abstract_State => State,
    Initializes => State,
    Initial_Condition => not Is_Thrown
is
    function Is_Thrown return Boolean with
        Global => (Input => State);
end E;
