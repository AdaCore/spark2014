with System.Storage_Elements;

package Volatiles_Illegal_Helper
  with SPARK_Mode
is
   X : Integer
     with Volatile,
          Async_Writers,
          Address => System.Storage_Elements.To_Address (16#BAD#);

   function F return Boolean
     with Global => X;

   generic
      Size : in Natural;
   package Gen is
      type T is new Integer range 1 .. Size;
   end Gen;
end Volatiles_Illegal_Helper;
