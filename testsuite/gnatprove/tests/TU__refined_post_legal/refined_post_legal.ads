package Refined_Post_Legal
  with SPARK_Mode,
       Abstract_State => State
is
   procedure Proc (Par  : in     Integer;
                   Par2 :    out Integer)
     with Global => State,
          Post   => Par2 >= Par;

   function Func (Par : Integer) return Integer
     with Global => State,
          Post   => Func'Result >= Par;
end Refined_Post_Legal;
