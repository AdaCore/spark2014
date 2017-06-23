
with Lib;

package Demo
with SPARK_Mode => On
is

   subtype T_Obit is Lib.T_OBIT;

   type T_Command_Id is (Cmd1, Cmd2);

end Demo;
