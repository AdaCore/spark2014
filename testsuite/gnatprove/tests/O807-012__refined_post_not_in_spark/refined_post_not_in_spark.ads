package Refined_Post_Not_In_SPARK
  with SPARK_Mode,
       Abstract_State => State
is
   procedure Proc (Par  : in     Integer;
                   Par2 :    out Integer)
     with Global => State,
          Post   => Par2 >= Par;

end;
