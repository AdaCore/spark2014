-------------------------------------------------------------------------------
-- Copyright: Omlis Ltd. 2015.  All rights reserved.
--
-- Omlis Confidential.
-- All information contained herein is and remains the property of Omlis Ltd.
-- The intellectual and technical concepts contained herein are proprietary to
-- Omlis Ltd. and may be covered by Patents or Patents in process and are
-- protected by trade secret or copyright law.  Dissemination of this material
-- or reproduction of this material is strictly forbidden unless prior written
-- permission is obtained from Omlis Ltd.
--
--  Decription:
--     This package provides a function to generate a Scrypt hash from an
--     unconstrained String.
--
---------------------------------------------------------------------------
with Interfaces;
with CommonTypes;
package Scrypt
with SPARK_Mode => On
is


   -----------------------------------------------------------------
   --  An utility function used to concat two byte arrays together
   --  it is used internally by PBKDF2HMACSHA256
   --
   --  Parameters:
   --    A   : The first array
   --    B   : The second array
   --
   --  Return Value:
   --    Ret := A || B; Where || denotes concat
   -----------------------------------------------------------------
   use CommonTypes;
   function Concat (A, B : in CommonTypes.ByteArray_t)
                    return CommonTypes.ByteArray_t with
     Pre => A /= CommonTypes.NULLByteArray
     and then B /= CommonTypes.NULLByteArray
     and then B'Length <= Integer'Last
     and then A'Last <= Integer'Last - B'Length
     and then A'Length - 1 <= Integer'Last - B'Length,
     Post => Concat'Result /= CommonTypes.NULLByteArray
     and then Concat'Result'Length  = A'Length + B'Length,
     Global => null;

end Scrypt;
