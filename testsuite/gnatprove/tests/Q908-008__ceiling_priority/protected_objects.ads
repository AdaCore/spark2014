pragma Profile (Ravenscar);

with Ada.Interrupts.Names; use Ada.Interrupts.Names;

package Protected_Objects
  with SPARK_Mode
is
   protected P is
      procedure Signal with Attach_Handler => SIGHUP;
   end P;

end Protected_Objects;
