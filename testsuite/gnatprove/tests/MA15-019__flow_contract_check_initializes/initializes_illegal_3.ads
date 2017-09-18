with Init_2; pragma Elaborate_All (Init_2);

package Initializes_Illegal_3
  with SPARK_Mode,
       Initializes => (X => Init_2.Z)  --  error: Z must be initialized at
                                       --         elaboration (of Init_2)
is
   X : Integer := Init_2.Z;
end Initializes_Illegal_3;
