with System; use System;
package Ext with SPARK_Mode is
   My_Global_Variable : constant Integer
   with
       Import,
       Volatile,
       Async_Writers,
       Address => System'To_Address (12);
   C : constant Integer with Volatile, Async_Writers, Import;

   function F return Integer is (C) with Volatile_Function;

   C1 : constant Integer := F;
   C2 : constant Integer := F;
   pragma Assert (C1 = C2);
end Ext;
