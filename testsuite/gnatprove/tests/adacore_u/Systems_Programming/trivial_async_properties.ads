with System.Storage_Elements;

package Trivial_Async_Properties
  with SPARK_Mode
is

   Ext_Address : constant System.Address :=
     System.Storage_Elements.To_Address (16#ABCD#);

   X : Integer with Volatile, Address => Ext_Address, Async_Readers;
   Y : Integer with Volatile, Address => Ext_Address, Async_Writers;

   procedure Set with
     Depends => (X    => null,
                 null => Y);

end Trivial_Async_Properties;
