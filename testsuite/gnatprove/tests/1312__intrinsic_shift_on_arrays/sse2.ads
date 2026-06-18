with Interfaces; use Interfaces;

package SSE2
with SPARK_Mode => On
is

   pragma Warnings (GNATprove, Off,
                    "pragma ""Machine_Attribute"" ignored (not yet supported)");

   -------------------------
   --  2x 64-bit vectors  --
   -------------------------

   package V2DI_Vectors
   is

      type V2DI_Index is range 0 .. 1;

      type V2DI is array (V2DI_Index) of Integer_64
        with Alignment => 16,
        Size => 128,
        Object_Size => 128;
      pragma Machine_Attribute (V2DI, "vector_type");
      pragma Machine_Attribute (V2DI, "may_alias");

      function "xor" (A, B : in V2DI) return V2DI
        with Global => null;
      pragma Import (Intrinsic, "xor", "__builtin_ia32_pxor128");

      function Shift_Left (A      : in V2DI;
                           Amount : in Natural) return V2DI
        with Global => null;
      pragma Import (Intrinsic, Shift_Left, "__builtin_ia32_psllqi128");

      function Shift_Right (A      : in V2DI;
                            Amount : in Natural) return V2DI
        with Global => null;
      pragma Import (Intrinsic, Shift_Right, "__builtin_ia32_psrlqi128");

      function Rotate_Left (A      : in V2DI;
                            Amount : in Natural) return V2DI
      is (Shift_Left (A, Amount) xor Shift_Right (A, 64 - Amount))
      with Inline,
      Global => null,
      Pre => Amount <= 64;

   end V2DI_Vectors;

end SSE2;
