with Ada.Text_IO;
package Carver_Test with
    SPARK_Mode => On,
    Annotate => Always_Return
is

    procedure Execute with
        Global => (In_Out => Ada.Text_IO.File_System);

end Carver_Test;
