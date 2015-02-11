package body Tree_Logic is


   procedure Insert
     (Branch   : in out Branch_Type;
      Iterator : in out Branch_Read_Iterator_Type)
   is
   begin
      Branch.M_Logical_Address := 0;
      Iterator.M_Is_Valid := False;
   end Insert;


end Tree_Logic;
