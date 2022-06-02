with My_Exception_Runtime; pragma Elaborate (My_Exception_Runtime);
with My_Lib;

procedure Main with
    Pre => not My_Exception_Runtime.My_Exceptions.Is_Thrown,
    SPARK_Mode => On
is

    package E renames My_Exception_Runtime.My_Exceptions;

    Result : My_Lib.Optional_Natural;
begin
    My_Lib.Try_Cast(42, Result);
    Pragma Assert(not E.Is_Thrown and then Result.Valid and then Result.Value = 42);

end Main;
