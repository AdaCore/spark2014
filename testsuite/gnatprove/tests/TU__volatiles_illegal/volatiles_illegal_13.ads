with System.Storage_Elements;

package Volatiles_Illegal_13
  with SPARK_Mode
is
   type Vol_Int_T is new Integer with Volatile;

   --  TU: 7. A non-volatile object shall not have a Volatile component.
   type Record_T is record
      A : Integer;
      B : Vol_Int_T;  --  Cannot have a volatile component in a non volatile
                      --  object.
   end record;
end Volatiles_Illegal_13;
