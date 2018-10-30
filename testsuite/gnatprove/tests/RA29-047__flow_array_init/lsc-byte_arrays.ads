with LSC.Types;

-- @summary
-- Extension of libsparkcryptos types by a byte array of unconstrained size
package LSC.Byte_Arrays
with SPARK_Mode
is

   -- Natural index type
   subtype Natural_Index is Natural range Natural'First .. Natural'Last - 1;

   -- Unconstrained byte array
   type Byte_Array_Type is array (Natural_Index range <>) of LSC.Types.Byte;

end LSC.Byte_Arrays;
