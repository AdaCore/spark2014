with P_Init; use P_Init;
with P_Print; use P_Print;

package body Run with SPARK_Mode is

   C1 : constant T (One) := T'(E  => One,
                         X1 => 1);
   C2 : constant T (Two) := T'(E  => Two,
                         X1 => 1,
                         X2 => 2);

   Y1 : T := C1;
   Y2 : T := C2;
   Z1 : T (One) := C1;
   Z2 : T (Two) := C2;

   procedure Run is
   begin
      -- OK
      Y2 := Init;
      Print ("Y2", Y2);
      Z2 := Init; --@DISCRIMINANT_CHECK:FAIL
      Print ("Z2", Z2);
      Y1 := Init;
      Print ("Y1", Y1);
      Y1 := C1;
      -- NOK
      Z1 := Init; --@DISCRIMINANT_CHECK:FAIL
      Print ("Z1", Z1);
   end Run;

end Run;
