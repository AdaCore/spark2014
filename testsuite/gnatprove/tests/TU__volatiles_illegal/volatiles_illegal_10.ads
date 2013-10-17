with System.Storage_Elements;

package Volatiles_Illegal_10
  --  TU: 12. A Volatile object shall only occur as an actual parameter of a
  --  subprogram if the corresponding formal parameter is of a non-scalar
  --  Volatile type or as an actual parameter in a call to an instance of
  --  Unchecked_Conversion.
  with SPARK_Mode
is
   type Vol_Scalar_T is mod 2**32 with Volatile;

   procedure Scalar_Formal_Parameter (Par : in out Vol_Scalar_T);
   --  Volatile formal parameter Par is a scalar.
end Volatiles_Illegal_10;
