with Init_2;

package Initializes_Illegal_2
  with SPARK_Mode,
       Abstract_State => (AS, AS2),
       Initializes    => (AS,
                          AS2 => null,
                          X   => Init_2.X,
                          Y   => Init_2.Y)
is
   pragma Elaborate_Body (Initializes_Illegal_2);

   X : Integer := Init_2.X;      --  OK
   Y : Integer := Init_2.Y + X;  --  warning: Y must not depend on X
end Initializes_Illegal_2;
