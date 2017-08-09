with System;

package Addr is

   X : Integer;

   Y : Integer;
   for Y'Address use X'Address;
   --  the above is fine as per RM

   function F return System.Address
     with SPARK_Mode => Off;

   Z : Integer;
   for Z'Address use F;
   --  the above should be rejected because of the use of a non-SPARK
   --  expression

end Addr;
