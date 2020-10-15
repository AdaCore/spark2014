with System;

package Problem_Types is
   type Data_Type is record
      status : Integer;
   end record with Size => 32;

   Problem_Var : Data_Type with
      Address => System'To_Address (16#1234_5678#);
end Problem_Types;
