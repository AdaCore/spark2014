package body Floats with SPARK_Mode is
Procedure Test (a : in T_Tab_3_Float;
                e : in out T_Tab_4_L_Float) is

b : T_Tab_4_L_Float := (0.0, 0.0, 0.0, 0.0);
c : T_Tab_4_L_Float := (0.0, 0.0, 0.0, 0.0);
d : T_Tab_4_L_Float := (0.0, 0.0, 0.0, 0.0);

Begin

pragma assert (A(1) in -1.0..1.0);
pragma assert (A(2) in -1.0..1.0);
pragma assert (A(3) in -1.0..1.0);

e(1) := 1.0;
e(2) := Long_Float (a(1)*0.5);
e(3) := Long_Float (a(2)*0.5);
e(4) := Long_Float (a(3)*0.5);

pragma assert (e(1) in -1.0..1.0);
pragma assert (e(2) in -1.0..1.0);
pragma assert (e(3) in -1.0..1.0);
pragma assert (e(4) in -1.0..1.0);
pragma assert (for all I in 1..4 => e(i) in -1.0..1.0);

c(1) := 1.0;
c(2) := Long_Float (a(1)*0.5);
c(3) := Long_Float (a(2)*0.5);
c(4) := Long_Float (a(3)*0.5);

pragma assert (c(1) in -1.0..1.0);
pragma assert (c(2) in -1.0..1.0);
pragma assert (c(3) in -1.0..1.0);
pragma assert (c(4) in -1.0..1.0);
pragma assert (for all I in 1..4 => c(i) in -1.0..1.0);

b(1) := 1.0;
b(2) := Long_Float (a(1)*0.5);
b(3) := Long_Float (a(2)*0.5);
b(4) := Long_Float (a(3)*0.5);

pragma assert (b(1) in -1.0..1.0);
pragma assert (b(2) in -1.0..1.0);
pragma assert (b(3) in -1.0..1.0);
pragma assert (b(4) in -1.0..1.0);
pragma assert (for all I in 1..4 => b(i) in -1.0..1.0);

d(1) := c(1) + b(1);
d(2) := c(2) + b(2);
d(3) := c(3) + b(3);
d(4) := c(4) + b(4);

pragma assert (d(1) in -2.0..2.0);
pragma assert (d(2) in -2.0..2.0);
pragma assert (d(3) in -2.0..2.0);
pragma assert (d(4) in -2.0..2.0);


end Test;
end Floats;
