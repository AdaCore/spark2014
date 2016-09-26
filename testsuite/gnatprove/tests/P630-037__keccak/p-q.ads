with P.Duplex;

pragma Elaborate_All (P.Duplex);

package P.Q
with SPARK_Mode => On
is

   package Duplex is new P.Duplex
     (State_Type => Integer);

end P.Q;
