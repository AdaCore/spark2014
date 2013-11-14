with F;
package P
  with SPARK_Mode => On,
       Initializes => (S => F.A)
is
   
   subtype R is Integer range 0 .. 10;
   
   S : R := F.Dyn; -- range check here!
   
end P;

   
