with U;
use type U.U32;
package P
  with SPARK_Mode => On
is

   --  Very simple test cases showing use of contracts
   --  on imported, intrinsic functions, such as U.Shift_Right
   procedure Op1 (A : in out U.U32)
     with Post => A = A'Old / 4;

   procedure Op2 (A : in out U.U32)
     with Post => A = A'Old / (2 ** 17);

end P;
