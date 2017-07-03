with System;

package P is

   C : constant System.Address := System'To_Address (16#50060800#);

   function Get_C return System.Address is (C);
   --  Constant initialized with a call to predefined function as a global

end;
