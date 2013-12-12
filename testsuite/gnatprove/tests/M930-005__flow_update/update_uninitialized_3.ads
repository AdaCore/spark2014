package Update_Uninitialized_3
  with SPARK_Mode,
       Abstract_State => State,
       Initializes    => State
is
   pragma Elaborate_Body (Update_Uninitialized_3);
end Update_Uninitialized_3;
