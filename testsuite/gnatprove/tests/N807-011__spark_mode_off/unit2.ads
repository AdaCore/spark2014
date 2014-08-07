with Unit1;

package Unit2 with
  SPARK_Mode => On
is
   procedure P with
     Global => (In_Out => Unit1.State);

   procedure Q with
     Global => (In_Out => Unit1.State);
end Unit2;
