limited with A;
With I;
use I;



package C with
  SPARK_Mode
is

   procedure calculer
     with SPARK_Mode,
   Global => (Input => A.Data);

end C;
