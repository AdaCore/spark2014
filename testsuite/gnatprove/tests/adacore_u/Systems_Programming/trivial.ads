with System.Storage_Elements;

package Trivial
  with SPARK_Mode
is

   Ext_Address : constant System.Address :=
     System.Storage_Elements.To_Address (16#ABCD#);

   X : Integer with Volatile, Address => Ext_Address;

   procedure Get (Val : out Integer) with
     Global  => (In_Out => X),
     Depends => (Val => X,
                 X   => X);

end Trivial;
