with System.Storage_Elements;

package Foo with SPARK_Mode
is
   pragma Elaborate_Body;

   type Vol_Rec_T is record
      X : Integer;
   end record;

   Vol2 : Vol_Rec_T
     with Volatile, Async_Writers,
          Address => System.Storage_Elements.To_Address (16#DEADBEEF#);

end Foo;
