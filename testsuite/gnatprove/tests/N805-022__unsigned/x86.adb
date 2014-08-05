package body X86
with SPARK_Mode
is

   function ECX return Unsigned_32 is
   begin
      return Unsigned_32(XCX(0)) + (Unsigned_32(XCX(1)) * (2**8)) +
        (Unsigned_32(XCX(2)) * (2**16)) + (Unsigned_32(XCX(3)) * (2**24));
   end ECX;

   procedure Write_ECX(val : in Unsigned_32) is
   begin
      XCX(0) := Unsigned_8(val rem 2**8);
      XCX(1) := Unsigned_8((val / (2**8)) rem 2**8);
      XCX(2) := Unsigned_8((val / (2**16)) rem 2**8);
      XCX(3) := Unsigned_8((val / (2**24)) rem 2**8);
      pragma Assert ((Unsigned_32(XCX(0)) +
                     (Unsigned_32(XCX(1)) * (2**8))) = (val rem 2**16));
      pragma Assert ((Unsigned_32(XCX(2)) +
                     (Unsigned_32(XCX(3)) * (2**8))) = ((val / (2**16)) rem 2**16));
      pragma Assert ((val rem 2**16) + (((val / (2**16)) rem 2**16) * 2**16) = val);
      pragma Assume (if (((Unsigned_32(XCX(0)) +
                     (Unsigned_32(XCX(1)) * (2**8))) = (val rem 2**16)) and
                       ((Unsigned_32(XCX(2)) +
                        (Unsigned_32(XCX(3)) * (2**8))) = ((val / (2**16)) rem 2**16)))
                     then ((Unsigned_32(XCX(0)) +
                       (Unsigned_32(XCX(1)) * (2**8)) +
                       (Unsigned_32(XCX(2)) * (2**16)) +
                       (Unsigned_32(XCX(3)) * (2**24))) = val));
      pragma Assert ((Unsigned_32(XCX(0)) +
                     (Unsigned_32(XCX(1)) * (2**8)) +
                     (Unsigned_32(XCX(2)) * (2**16)) +
                     (Unsigned_32(XCX(3)) * (2**24))) = val);
   end Write_ECX;

   function ESI return Unsigned_32 is
   begin
      return Unsigned_32(XSI(0)) + (Unsigned_32(XSI(1)) * (2**8)) +
        (Unsigned_32(XSI(2)) * (2**16)) + (Unsigned_32(XSI(3)) * (2**24));
   end ESI;

   procedure Write_ESI(val : in Unsigned_32) is
   begin
      XSI(0) := Unsigned_8(val rem 2**8);
      XSI(1) := Unsigned_8((val / (2**8)) rem 2**8);
      XSI(2) := Unsigned_8((val / (2**16)) rem 2**8);
      XSI(3) := Unsigned_8((val / (2**24)) rem 2**8);
      pragma Assert ((Unsigned_32(XSI(0)) +
                     (Unsigned_32(XSI(1)) * (2**8))) = (val rem 2**16));
      pragma Assert ((Unsigned_32(XSI(2)) +
                     (Unsigned_32(XSI(3)) * (2**8))) = ((val / (2**16)) rem 2**16));
      pragma Assert ((val rem 2**16) + (((val / (2**16)) rem 2**16) * 2**16) = val);
      pragma Assume (if (((Unsigned_32(XSI(0)) +
                     (Unsigned_32(XSI(1)) * (2**8))) = (val rem 2**16)) and
                       ((Unsigned_32(XSI(2)) +
                        (Unsigned_32(XSI(3)) * (2**8))) = ((val / (2**16)) rem 2**16)))
                     then ((Unsigned_32(XSI(0)) +
                       (Unsigned_32(XSI(1)) * (2**8)) +
                       (Unsigned_32(XSI(2)) * (2**16)) +
                       (Unsigned_32(XSI(3)) * (2**24))) = val));
      pragma Assert ((Unsigned_32(XSI(0)) +
                     (Unsigned_32(XSI(1)) * (2**8)) +
                     (Unsigned_32(XSI(2)) * (2**16)) +
                     (Unsigned_32(XSI(3)) * (2**24))) = val);
   end Write_ESI;

   function EDI return Unsigned_32 is
   begin
      return Unsigned_32(XDI(0)) + (Unsigned_32(XDI(1)) * (2**8)) +
        (Unsigned_32(XDI(2)) * (2**16)) + (Unsigned_32(XDI(3)) * (2**24));
   end EDI;

   procedure Write_EDI(val : in Unsigned_32) is
   begin
      XDI(0) := Unsigned_8(val rem 2**8);
      XDI(1) := Unsigned_8((val / (2**8)) rem 2**8);
      XDI(2) := Unsigned_8((val / (2**16)) rem 2**8);
      XDI(3) := Unsigned_8((val / (2**24)) rem 2**8);
      pragma Assert ((Unsigned_32(XDI(0)) +
                     (Unsigned_32(XDI(1)) * (2**8))) = (val rem 2**16));
      pragma Assert ((Unsigned_32(XDI(2)) +
                     (Unsigned_32(XDI(3)) * (2**8))) = ((val / (2**16)) rem 2**16));
      pragma Assert ((val rem 2**16) + (((val / (2**16)) rem 2**16) * 2**16) = val);
      pragma Assume (if (((Unsigned_32(XDI(0)) +
                     (Unsigned_32(XDI(1)) * (2**8))) = (val rem 2**16)) and
                       ((Unsigned_32(XDI(2)) +
                        (Unsigned_32(XDI(3)) * (2**8))) = ((val / (2**16)) rem 2**16)))
                     then ((Unsigned_32(XDI(0)) +
                       (Unsigned_32(XDI(1)) * (2**8)) +
                       (Unsigned_32(XDI(2)) * (2**16)) +
                       (Unsigned_32(XDI(3)) * (2**24))) = val));
      pragma Assert ((Unsigned_32(XDI(0)) +
                     (Unsigned_32(XDI(1)) * (2**8)) +
                     (Unsigned_32(XDI(2)) * (2**16)) +
                     (Unsigned_32(XDI(3)) * (2**24))) = val);
   end Write_EDI;

   function ReadMem8(addr : in Unsigned_64) return Unsigned_8
   is
   begin
      return Memory(addr);
   end ReadMem8;

   -- Note that if addr is Unsigned_64'Last, this will take the last byte in
   -- Memory as the "low" byte and the first byte in Memory as the "high" byte
   function ReadMem16(addr: in Unsigned_64) return Unsigned_16
   is
   begin
      return Unsigned_16(ReadMem8(addr)) +
        (Unsigned_16(ReadMem8(addr + 1)) * (2**8));
   end ReadMem16;

   -- See note for ReadMem16, but this can wrap around 3 different ways
   function ReadMem32(addr: in Unsigned_64) return Unsigned_32
   is
   begin
      return Unsigned_32(ReadMem16(addr)) +
        (Unsigned_32(ReadMem16(addr + 2)) * (2**16));
   end ReadMem32;

   -- Saves a 32-bit value to Memory
   -- Note that this will wrap if addr > 2**64-3
   procedure WriteMem32(addr : in Unsigned_64; val : in Unsigned_32)
   is
   begin
      Memory(addr) := Unsigned_8(val rem 2**8);
      Memory(addr + 1) := Unsigned_8((val / (2**8)) rem 2**8);
      Memory(addr + 2) := Unsigned_8((val / (2**16)) rem 2**8);
      Memory(addr + 3) := Unsigned_8((val / (2**24)) rem 2**8);
      pragma Assert ((Unsigned_32(Memory(addr)) +
                     (Unsigned_32(Memory(addr + 1)) * (2**8))) = (val rem 2**16));
      pragma Assert ((Unsigned_32(Memory(addr + 2)) +
                     (Unsigned_32(Memory(addr + 3)) * (2**8))) = ((val / (2**16)) rem 2**16));
      pragma Assert ((val rem 2**16) + (((val / (2**16)) rem 2**16) * 2**16) = val);
      pragma Assume (if (((Unsigned_32(Memory(addr)) +
                     (Unsigned_32(Memory(addr + 1)) * (2**8))) = (val rem 2**16)) and
                       ((Unsigned_32(Memory(addr + 2)) +
                        (Unsigned_32(Memory(addr + 3)) * (2**8))) = ((val / (2**16)) rem 2**16)))
                     then ((Unsigned_32(Memory(addr)) +
                       (Unsigned_32(Memory(addr + 1)) * (2**8)) +
                       (Unsigned_32(Memory(addr + 2)) * (2**16)) +
                       (Unsigned_32(Memory(addr + 3)) * (2**24))) = val));
      pragma Assert ((Unsigned_32(Memory(addr)) +
              (Unsigned_32(Memory(addr + 1)) * (2**8)) +
              (Unsigned_32(Memory(addr + 2)) * (2**16)) +
                     (Unsigned_32(Memory(addr + 3)) * (2**24))) = val);
   end WriteMem32;

   -- repe32 uses ESI and EDI as the location of memory addresses to compare
   -- and ECX as the counter
   procedure repe32_cmpsb
   is
      val1, val2: Unsigned_8;
   begin
      repe_loop:
      while (ECX /= 0) loop
         pragma Assert (ECX /= 0);
         -- TODO: when logic is added to deal with interrupts, that code should
         -- be added here
         val1 := ReadMem8(Unsigned_64(ESI));
         val2 := ReadMem8(Unsigned_64(EDI));
         ZeroFlag := ((val1 - val2) = 0);
         CarryFlag := (Unsigned_16(val1) + Unsigned_16(val2) >
                      Unsigned_16(val1 + val2));
         Write_ECX(ECX - 1);
         exit repe_loop when ((ECX = 0) or (not ZeroFlag));
         Write_ESI(ESI + 1);
         Write_EDI(EDI + 1);
      end loop repe_loop;
      pragma Assume ((ECX = 0) or (not ZeroFlag));
   end repe32_cmpsb;

end X86;

