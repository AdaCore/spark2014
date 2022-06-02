generic

    type Cause_Type is private;
    with function "="(Lhs, Rhs : Cause_Type) return Boolean;
    with procedure Report_Exception(Cause : Cause_Type);

package Exceptions with
    SPARK_Mode => On,
    Abstract_State => (State),
    Initializes => (State),
    Initial_Condition => (not Is_Thrown)
is

    function Is_Thrown return Boolean with
        Global => (Input => State),
        Ghost;

    function Get_Cause return Cause_Type with
        Global => (Input => State),
        Ghost,
        Pre => Is_Thrown;

    procedure Throw(Cause : Cause_Type) with
        Global => (In_Out => State),
        Pre => (not Is_Thrown),
        Post => (Is_Thrown and then Get_Cause = Cause);

end Exceptions;
