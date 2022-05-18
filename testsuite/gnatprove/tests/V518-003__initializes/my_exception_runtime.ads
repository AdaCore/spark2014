with Exceptions;

package My_Exception_Runtime with
   SPARK_Mode => On,
   Initial_Condition => not My_Exceptions.Is_Thrown
is

    type Error_Message_Type is array (Positive range 1 .. 32) of Character;

    procedure Die(Error_Message : Error_Message_Type);

    package My_Exceptions is new Exceptions(Error_Message_Type, "=", Die);-- with
        --Initializes => My_Exceptions.State;

end My_Exception_Runtime;
