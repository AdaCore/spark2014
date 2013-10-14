package Refined_Depends_Legal
  with SPARK_Mode,
       Abstract_State => (S, S2, S3, S_Null, S_Null2),
       Initializes    => (S, S2, S3, S_Null, S_Null2)
is
   procedure P1 (Par1 : in     Integer;
                 Par2 :    out Integer;
                 Par3 : in out Integer)
     with Global  => (Input  => S,
                      Output => (S2, S_Null2),
                      In_Out => S_Null),
          Depends => (Par2          =>  (S_Null, Par1, S),
                      Par3          =>+ S_Null,
                      (S2, S_Null2) =>  (S, Par3),
                      S_Null        =>  S_Null);

   procedure P2
     with Global  => (In_Out => S3),
          Depends => (S3 => S3);
end Refined_Depends_Legal;
