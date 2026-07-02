procedure Backend_Switches with SPARK_Mode is

   --  On a 64-bit target, Long_Integer is a 64-bit type, so the addition
   --  below cannot overflow given the precondition. On a 32-bit target
   --  (as selected by the code-generation switch -m32), Long_Integer is a
   --  32-bit type and the very same addition overflows.
   --
   --  GNATprove analyses with the host (64-bit) target model even when the
   --  code is compiled with -m32 and no matching target configuration file
   --  is supplied. It therefore discharges the overflow check below, which
   --  is unsound: the compiled program overflows at run time.

   function Add (X, Y : Long_Integer) return Long_Integer
   with Pre => X in 0 .. 2 ** 30 and then Y in 0 .. 2 ** 30;

   function Add (X, Y : Long_Integer) return Long_Integer
   is (X + Y);

   --  A second, self-contained witness of the same model mismatch: the
   --  front end reports Long_Integer as 64-bit, but with -m32 it is 32-bit.

   pragma Assert (Long_Integer'Size = 64); --@ASSERT:FAIL

begin
   null;
end Backend_Switches;
