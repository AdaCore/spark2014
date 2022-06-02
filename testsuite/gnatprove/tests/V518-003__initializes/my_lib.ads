with My_Exception_Runtime;

package My_Lib with
    SPARK_Mode => On
is

    package E renames My_Exception_Runtime.My_Exceptions;
    use type My_Exception_Runtime.Error_Message_Type;

    Cast_Error_Message : constant My_Exception_Runtime.Error_Message_Type :=
        "Negative input!                 ";

    type Optional_Natural(Valid : Boolean := False) is record
        case Valid is
            when True =>
                Value : Natural;
            when False =>
                null;
        end case;
    end record;

    No_Natural : constant Optional_Natural := Optional_Natural'(Valid => False);
    function Optionalize(V : Natural) return Optional_Natural is
        (Optional_Natural'(Valid => True, Value => V));

    procedure Try_Cast(Input : Integer; Output : out Optional_Natural) with
        Pre => (not E.Is_Thrown and then not Output'Constrained),
        Contract_Cases => (
            Input >= 0 => (not E.Is_Thrown and then Output = Optionalize(Input)),
            Input < 0 => (E.Is_Thrown and then E.Get_Cause = Cast_Error_Message and then
                Output = No_Natural)
        );

end My_Lib;
