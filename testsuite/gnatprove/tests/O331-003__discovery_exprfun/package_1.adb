package body Package_1
   with SPARK_Mode => On
is
   Const_1 : constant := 0.01;
   Const_2 : constant := 1.23;

   procedure Update (InputVar  : in     Restricted_Float;
                     OutputVar :    out Float)
   is
      function Calculate return Float
      is
         (InputVar * Const_1);
   begin

      OutputVar := Calculate + Const_2; --@OVERFLOW_CHECK:PASS

   end Update;

end Package_1;
