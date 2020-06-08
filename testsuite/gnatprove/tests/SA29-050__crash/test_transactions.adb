pragma SPARK_Mode(On);

with Ada.Text_IO;

package body Test_Transactions is
    procedure Test_Transaction is
        use Data_Read_Status;

        Status: Data_Read_Status.Status_Type; -- := Initial_Status;
    begin
        Ada.Text_IO.Put_Line("dummy text");
    end Test_Transaction;
end Test_Transactions;
