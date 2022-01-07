with Interfaces;
use Interfaces;

package X86
  with SPARK_Mode
is
   subtype Unsigned64 is Interfaces.Unsigned_64;
   subtype Unsigned32 is Interfaces.Unsigned_32;
   subtype Unsigned16 is Interfaces.Unsigned_16;
   subtype Unsigned8  is Interfaces.Unsigned_8;

   -----------------------------------------------------------------------
   --		   Definition of AL, AH, AX, EAX, and RAX		--
   -----------------------------------------------------------------------

   RAX : Unsigned64 := 0;

   function AL return Unsigned8 with
     Global => (Input => RAX),
     Post => (AL'Result = Unsigned8(RAX and 16#00000000000000FF#));

   procedure Write_AL(Val : in Unsigned8) with
     Global => (In_Out => RAX),
     Post => (RAX = ((RAX'Old and 16#FFFFFFFFFFFFFF00#) or Unsigned64(Val)));

   function AH return Unsigned8 with
     Global => (Input => RAX),
     Post => (AH'Result = Unsigned8'Mod((RAX and 16#000000000000FF00#) / 256));

   procedure Write_AH(Val : in Unsigned8) with
     Global => (In_Out => RAX),
     Post => (RAX = ((RAX'Old and 16#000000000000FF00#) or Unsigned64(Unsigned16(Val) * 256)));

   -- Returns the Value of bits 1-16 from RAX
   function AX return Unsigned16 with
     Global => (Input => RAX),
     Post => (AX'Result = Unsigned16(RAX and 16#000000000000FFFF#));

   procedure Write_AX(Val : in Unsigned16) with
     Global => (In_Out => RAX),
     Post => (RAX = ((RAX'Old and 16#FFFFFFFFFFFF0000#) or Unsigned64(Val)));

   function EAX return Unsigned32 with
     Global => (Input => RAX),
     Post   => (EAX'Result = Unsigned32(RAX and 16#00000000FFFFFFFF#));

   procedure Write_EAX(Val : in Unsigned32) with
     Global => (In_Out => RAX),
     Post   => (RAX = ((RAX'Old and 16#FFFFFFFF00000000#) or Unsigned64(Val)));

   -----------------------------------------------------------------------
   --			            Main     	        		--
   -----------------------------------------------------------------------

   procedure Main with
     Global => (In_Out => RAX),
     Post   => (AL = 1); --@POSTCONDITION:PASS

   -----------------------------------------------------------------------
   --			      Read/Write Memory 			--
   -----------------------------------------------------------------------
   -- This array models 2**64 8-bit elements of memory
   type Mem_Array is array (Unsigned64) of Unsigned8;

   Memory	    : Mem_Array   := Mem_Array'(others => 0);

   -- Saves a 64-bit Value to Memory
   -- Note that this will wrap if addr > 2**64-7
   procedure WriteMem64(addr : in Unsigned64; Val : in Unsigned64) with
     Global => (In_Out => Memory),
     Post => (((Unsigned64(Memory(addr)) or
	      Shift_Left(Unsigned64(Memory(addr + 1)),8) or
                  Shift_Left(Unsigned64(Memory(addr + 2)),16) or
                  Shift_Left(Unsigned64(Memory(addr + 3)),24) or
                  Shift_Left(Unsigned64(Memory(addr + 4)),32) or
                  Shift_Left(Unsigned64(Memory(addr + 5)),40) or
                  Shift_Left(Unsigned64(Memory(addr + 6)),48) or
                  Shift_Left(Unsigned64(Memory(addr + 7)),56)) = Val) and
		(for all i in Unsigned64 =>
		     (if ((i /= addr) and (i /= addr + 1) and
			    (i /= addr + 2) and (i /= addr + 3) and
			    (i /= addr + 4) and (i /= addr + 5) and
			    (i /= addr + 6) and (i /= addr + 7)) then
			  (Memory(i) = Memory'Old(i)))));

end X86;
