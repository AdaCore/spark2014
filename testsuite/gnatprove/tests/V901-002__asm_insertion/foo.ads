with x86_64_linux_gnu_bits_stdint_uintn_h;
use x86_64_linux_gnu_bits_stdint_uintn_h;
with Interfaces.C;
use Interfaces.C;
package Foo with SPARK_Mode => On is
   type Eight_Byte_Array is array (1 .. 8) of uint8_t;
   function Check (Input : Eight_Byte_Array) return Natural with
      Post => Check'Result >= 0 and then Check'Result < 4,
      Global        => null,
      Depends       => (Check'Result => Input),
      Export        => True,
      Convention    => C,
      External_Name => "foo__check";
end Foo;
