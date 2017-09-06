with System.Storage_Elements;

package Trivial_No_Output
  with SPARK_Mode
is

   Ext_Address : constant System.Address :=
     System.Storage_Elements.To_Address (16#ABCD#);

   X : Integer with Volatile, Address => Ext_Address,
     Async_Readers, Async_Writers, Effective_Writes;

   procedure Get (Val : out Integer) with
     Global  => (Input => X),
     Depends => (Val => X);

end Trivial_No_Output;
