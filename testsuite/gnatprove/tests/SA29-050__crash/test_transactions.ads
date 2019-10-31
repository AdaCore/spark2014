pragma SPARK_Mode(On);

with Data_Accessors;
use  Data_Accessors;

package Test_Transactions is

    package Data_Read_Status is new Data_Status;

    procedure Test_Transaction;

end Test_Transactions;
