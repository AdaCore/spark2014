with System.Storage_Elements;

package Volatiles_Illegal_5
  with SPARK_Mode
is
   --  TU: 6. A constant, a discriminant or a loop parameter shall not be
   --  Volatile.
   Const_Vol : constant Integer
     with Volatile,
          Address => System.Storage_Elements.To_Address (16#A110#);

   type Vol_Int_T is new Integer with Volatile;

   Vol_Var : Vol_Int_T
     with Address => System.Storage_Elements.To_Address (16#A220#);

   procedure Vol_Loop_Par (Par : in out Integer);
end Volatiles_Illegal_5;
