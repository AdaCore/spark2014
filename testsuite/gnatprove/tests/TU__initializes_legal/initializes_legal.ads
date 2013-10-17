with Initializes_Legal_Helper;
use  Initializes_Legal_Helper;

package Initializes_Legal
  with SPARK_Mode,
       Abstract_State => (S1,
                          (S2 with External => Async_Writers),
                          (S3 with External => Async_Readers),
                          (S4 with External)),
       Initializes    => (S1,
                          S2,
                          S3,
                          S4 => SH1,
                          X  => (SH1, Var_H1))
is
   X : Integer;

   package Embedded
     with Abstract_State => ES1,
          Initializes    => null
   is
      Y : Natural;
   end Embedded;

   procedure P1;
end Initializes_Legal;
