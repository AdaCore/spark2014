private package Hierarchical_State_Demo.A_Pack
   with SPARK_Mode => On,
        Abstract_State => (State with Part_Of => Top_State),
        Initializes    => State
is
   procedure A_Proc (Test : in out Natural)
      with Global   => (In_Out =>  State),
           Depends  => (Test   =>+ State,
                        State  =>+ Test);
end Hierarchical_State_Demo.A_Pack;
