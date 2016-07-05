with X86;
use type X86.Unsigned64;
use type X86.Unsigned32;
use type X86.Unsigned8;

package C_Library
  with SPARK_Mode
is

   subtype Unsigned64 is X86.Unsigned64;
   subtype Unsigned32 is X86.Unsigned32;
   subtype Unsigned8 is X86.Unsigned8;

   dummy_var : Unsigned64 := 0;

   procedure printf_chk with
     Global => (Input => X86.R8,
		In_Out => (Dummy_Var, X86.RSP)),
     Post => ((dummy_var = dummy_var'Old + X86.R8) AND (X86.RSP = X86.RSP'Old + 8));

   procedure puts with
     Global => (In_Out => X86.RSP),
     Post => (X86.RSP = X86.RSP'Old + 8);

   procedure putchar with
     Global => (In_Out => X86.RSP),
     Post => (X86.RSP = X86.RSP'Old + 8);

   procedure isoc99_scanf with
     Global => (In_Out => X86.RSP),
     Post => (X86.RSP = X86.RSP'Old + 8);

   procedure getuid with
     Global => (In_Out => X86.RSP),
     Post => (X86.RSP = X86.RSP'Old + 8);

   -- First input parameter is RDI register in x86_64 code.
   procedure setuid with
     Global => (Input  => (X86.RDI),
		In_Out => (Dummy_Var, X86.RSP)),
     Pre => (X86.RDI /= 0),
     Post => ((dummy_var = dummy_var'Old + Unsigned64(X86.EDI)) AND
                  (X86.RSP = X86.RSP'Old + 8));

   procedure stack_chk_fail with
     Global => (In_Out => X86.RSP),
     Post => (X86.RSP = X86.RSP'Old + 8);

   procedure Zephyr_exit with
     Global => (In_Out => X86.RSP),
     Post => (X86.RSP = X86.RSP'Old + 8);

end C_Library;
