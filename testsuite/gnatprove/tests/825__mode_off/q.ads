with PP;

package Q
with SPARK_Mode => On
is
   function F (X : Boolean) return PP.SUBENUM is
     (if X then PP.A else PP.A);
end Q;
