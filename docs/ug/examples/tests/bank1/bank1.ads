with Account1; use Account1;
package Bank1 with
  SPARK_Mode
is
   Special_Accounts : Account_Management;

   type Account_Type is (Regular, Premium, Selective);
   type Account_Array is array (Account_Type) of Account_Management;
   All_Accounts : Account_Array;
end Bank1;
