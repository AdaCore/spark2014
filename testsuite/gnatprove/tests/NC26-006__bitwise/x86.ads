with Interfaces;
use Interfaces;

package X86
  with SPARK_Mode
is
   subtype Unsigned64 is Interfaces.Unsigned_64;
   subtype Unsigned32 is Interfaces.Unsigned_32;
   subtype Unsigned16 is Interfaces.Unsigned_16;
   subtype Unsigned8  is Interfaces.Unsigned_8;


      -- This array models 2**64 8-bit elements of memory
   type Mem_Array is array (Unsigned64) of Unsigned8;

   Memory	    : Mem_Array   := Mem_Array'(others => 0);


   function ReadMem8(addr : in Unsigned64) return Unsigned8 with
     Global => (Input => Memory),
     Post => (ReadMem8'Result = Memory(addr));

   function ReadMem16(addr: in Unsigned64) return Unsigned16 with
     Global => (Input => Memory),
     Post => (ReadMem16'Result = (Unsigned16(Memory(addr)) or
                  Shift_Left(Unsigned16(Memory(addr+1)),8)));

   function ReadMem32(addr: in Unsigned64) return Unsigned32 with
     Global => (Input => Memory),
     Post => (ReadMem32'Result = (Unsigned32(ReadMem16(addr)) or --@POSTCONDITION:PASS
                  Shift_Left(Unsigned32(ReadMem16(addr + 2)),16)));


   function ReadMem32_v2(addr: in Unsigned64) return Unsigned32 with
     Global => (Input => Memory),
     Post => (ReadMem32_v2'Result = (Unsigned32(ReadMem16(addr)) or
                  Shift_Left(Unsigned32(ReadMem16(addr + 2)),16)));


end X86;
