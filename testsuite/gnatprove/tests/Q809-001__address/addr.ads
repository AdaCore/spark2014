with System;

package Addr is

   X : Integer;

   Y : Integer;
   for Y'Address use X'Address;
   --  the above is fine as per RM

   function F return System.Address
     with SPARK_Mode => Off;

end Addr;
