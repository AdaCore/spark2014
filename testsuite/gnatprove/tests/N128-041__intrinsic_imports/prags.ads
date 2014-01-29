package Prags
  with SPARK_Mode => On
is
   type M1 is mod 2**32;

   type Int1 is new Integer;
   type Int2 is new Integer;

   type PI1 is private;
   type PI2 is private;

   -- Import of Intrinsic Shift function for a user-defined
   -- modular type.  See GNAT RM Section 7.
   -- Explicit Global => null, so no warning.
   --
   -- This example uses pragmas
   function Shift_Left (Value  : M1;
                        Amount : Natural) return M1;
   pragma Global (null);
   pragma Import (Intrinsic, Shift_Left);

   -- This example uses aspects to achieve the same
   function Shift_Right (Value  : M1;
                         Amount : Natural) return M1
     with Global => null,
          Import,
          Convention => Intrinsic;

   -- Same as above, but no Global aspect.
   -- For Intrinsic functions, Global => null is assumed,
   -- so no warning.
   function Rotate_Right (Value  : M1;
                          Amount : Natural) return M1
     with Import,
          Convention => Intrinsic;

   -- Intrinsic operator for mixed types
   --
   -- Also assumed to have Global => null, so no
   -- explicit Global is needed, and no warning.
   function "+" (Left : Int1; Right : Int2) return Int1
     with Import,
          Convention => Intrinsic;

   -- As above, but private types
   function "-" (Left : PI1; Right : PI2) return PI1
     with Import,
          Convention => Intrinsic;


   -- Function Imported from C, so NOT Intrinsic.
   -- Warning expected here that Global => null has been assumed
   function F1 (Left, Right : M1) return M1
     with Import,
          Convention => C;

   -- Function Imported from C, so NOT Intrinsic.
   -- Explicit Global aspect, so no warning
   function F2 (Left, Right : M1) return M1
     with Global => null,
          Import,
          Convention => C;
private
   type PI1 is new Integer;
   type PI2 is new Integer;
end Prags;

