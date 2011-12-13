package body Report is

     No_Name : constant String (1..7) := "NO_NAME";

     Test_Name : String (1..15);

     function Time_Stamp return String is
     begin
        return "TODAY";
     end Time_Stamp;

begin
     Test_Name_Len := No_Name'Length;
     Test_Name (1..Test_Name_Len) := No_Name;
END REPORT;
