with System.Storage_Elements;

package Trivial_Effective_Properties
  with SPARK_Mode
is

   Ext_Address : constant System.Address :=
     System.Storage_Elements.To_Address (16#ABCD#);

   X : Integer with Volatile, Address => Ext_Address,
     Effective_Writes, Async_Readers;
   Y : Integer with Volatile, Address => Ext_Address,
     Effective_Reads, Async_Writers;

   procedure Set with
     Depends => (X => Y,
                 Y => Y);

end Trivial_Effective_Properties;
