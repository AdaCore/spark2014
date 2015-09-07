package Hierarchical_State_Demo
   with Spark_Mode     => On,
        Abstract_State => Top_State,
        Initializes    => Top_State
is
   procedure Do_Something (Value   : in out Natural;
                           Success :    out Boolean)
      with Global  => (In_Out => Top_State),
           Depends => (Value     =>+ Top_State,
                       Success   => (Value, Top_State),
                       Top_State =>+ Value);
end Hierarchical_State_Demo;
