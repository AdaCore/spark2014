with Ada.Text_IO;
with GNAT.OS_Lib;

package body My_Exception_Runtime with
    SPARK_Mode => Off
is

    procedure Die(Error_Message : Error_Message_Type) is begin
        Ada.Text_IO.Put_Line(String(Error_Message));
        GNAT.OS_Lib.OS_Exit(1);
    end Die;

end My_Exception_Runtime;
