package Foo
is
   -- Tests for Linker_Section (from the GNAT RM)

   Port_A : Integer;
   pragma Volatile (Port_A);
   pragma Linker_Section (Port_A, ".bss.port_a");

   Port_B : Integer;
   pragma Volatile (Port_B);
   pragma Linker_Section (Port_B, ".bss.port_b");

   type Port_Type is new Integer with Linker_Section => ".bss";
   PA : Port_Type with Linker_Section => ".bss.PA";
   PB : Port_Type; --  ends up in linker section ".bss"

   procedure Q with Linker_Section => "Qsection";

end Foo;
