package Depends_Legal
  with SPARK_Mode,
       Abstract_State => (A1,
                          (A2 with External => Async_Writers),
                          (A3 with External => Async_Readers))
is
   type Rec is
      record
         A, B : Integer;
      end record;

   X, Y : Integer;
   Comp : Rec;

   procedure P1
     --  dependency_relation ::= null
     with Depends => null;


   procedure P2 (Par1 : Integer)
     --  dependency_relation ::= dependency_clause
     with Global  => (Output => X),
          Depends => (X => Par1);


   procedure P3 (Par1 : Integer ; Par2 : in out Integer)
     --  dependency_relation ::= dependency_clause {, dependency_clause}
     with Global  => (In_Out => Comp,
                      Output => (X, A3),
                      Input  => (A1, A2, Y)),
          Depends => (X    =>  Par1,
                      Comp =>+ Par1,
                      Par2 =>+ null,
                      A3   =>  (A2, A1),
                      null =>  Y);


   function F1 (Par1 : in Integer) return Integer
     --  a function's result can appear as a depend's output
     with Depends => (F1'Result => null,
                      null      => Par1);
end Depends_Legal;
