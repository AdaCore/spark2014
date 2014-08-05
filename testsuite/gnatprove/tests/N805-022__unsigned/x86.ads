package X86
with SPARK_Mode
is
   type Unsigned_64 is mod 2**64;
   type Unsigned_32 is mod 2**32;
   type Unsigned_16 is mod 2**16;
   type Unsigned_8  is mod 2**8;

   -- This array models 2**64 8-bit elements of memory
   type Mem_Array is array (Unsigned_64) of Unsigned_8;

   subtype Count8 is Natural range 0..7;
   -- Represents 64-bits as 8 8-bit values
   type Reg_Type is array (Count8) of Unsigned_8;

   ZeroFlag         : Boolean     := false;
   CarryFlag        : Boolean     := false;
   Memory           : Mem_Array   := Mem_Array'(others => 0);

   XCX : Reg_Type := Reg_Type'(others => 0);

   function ECX return Unsigned_32 with
     Global => (Input => XCX),
     Post   => (ECX'Result = Unsigned_32(XCX(0)) +
                (Unsigned_32(XCX(1)) * (2**8)) +
                (Unsigned_32(XCX(2)) * (2**16)) +
                (Unsigned_32(XCX(3)) * (2**24)));

   procedure Write_ECX(val : in Unsigned_32) with
     Global => (In_Out => XCX),
     Post   => (((Unsigned_32(XCX(0)) +
                (Unsigned_32(XCX(1)) * (2**8)) +
                (Unsigned_32(XCX(2)) * (2**16)) +
                (Unsigned_32(XCX(3)) * (2**24))) = val) and
                  (for all I in 4..7 =>
                       XCX(I) = XCX'Old(I)));

   XSI : Reg_Type := Reg_Type'(others => 0);

   function ESI return Unsigned_32 with
     Global => (Input => XSI),
     Post   => (ESI'Result = Unsigned_32(XSI(0)) +
                (Unsigned_32(XSI(1)) * (2**8)) +
                (Unsigned_32(XSI(2)) * (2**16)) +
                (Unsigned_32(XSI(3)) * (2**24)));

   procedure Write_ESI(val : in Unsigned_32) with
     Global => (In_Out => XSI),
     Post   => (((Unsigned_32(XSI(0)) +
                (Unsigned_32(XSI(1)) * (2**8)) +
                (Unsigned_32(XSI(2)) * (2**16)) +
                (Unsigned_32(XSI(3)) * (2**24))) = val) and
                  (for all I in 4..7 =>
                       XSI(I) = XSI'Old(I)));

   XDI : Reg_Type := Reg_Type'(others => 0);

   function EDI return Unsigned_32 with
     Global => (Input => XDI),
     Post   => (EDI'Result = Unsigned_32(XDI(0)) +
                (Unsigned_32(XDI(1)) * (2**8)) +
                (Unsigned_32(XDI(2)) * (2**16)) +
                (Unsigned_32(XDI(3)) * (2**24)));

   procedure Write_EDI(val : in Unsigned_32) with
     Global => (In_Out => XDI),
     Post   => (((Unsigned_32(XDI(0)) +
                (Unsigned_32(XDI(1)) * (2**8)) +
                (Unsigned_32(XDI(2)) * (2**16)) +
                (Unsigned_32(XDI(3)) * (2**24))) = val) and
                  (for all I in 4..7 =>
                       XDI(I) = XDI'Old(I)));

   function ReadMem8(addr : in Unsigned_64) return Unsigned_8 with
     Global => (Input => Memory),
     Post => ((ReadMem8'Result = Memory(addr)) and (ReadMem8'Result >= 0));

   -- Note that if addr is Unsigned_64'Last, this will take the last byte in
   -- Memory as the "low" byte and the first byte in Memory as the "high" byte
   function ReadMem16(addr: in Unsigned_64) return Unsigned_16 with
     Global => (Input => Memory),
     Post => ((ReadMem16'Result = Unsigned_16(Memory(addr)) +
              (Unsigned_16(Memory(addr + 1)) * (2**8))) and
                (ReadMem16'Result >= 0));

   -- See note for ReadMem16, but this can wrap around 3 different ways
   function ReadMem32(addr: in Unsigned_64) return Unsigned_32 with
     Global => (Input => Memory),
     Post => ((ReadMem32'Result = Unsigned_32(ReadMem16(addr)) +
              (Unsigned_32(ReadMem16(addr + 2)) * (2**16))) and
                (ReadMem32'Result >= 0));

   -- Saves a 32-bit value to Memory
   -- Note that this will wrap if addr > 2**64-3
   procedure WriteMem32(addr : in Unsigned_64; val : in Unsigned_32) with
     Global => (In_Out => Memory),
     Post => (((Unsigned_32(Memory(addr)) +
              (Unsigned_32(Memory(addr + 1)) * (2**8)) +
              (Unsigned_32(Memory(addr + 2)) * (2**16)) +
              (Unsigned_32(Memory(addr + 3)) * (2**24))) = val) and
                (for all i in Unsigned_64 =>
                     (if ((i /= addr) and (i /= addr + 1) and
                          (i /= addr + 2) and (i /= addr + 3)) then
                          (Memory(i) = Memory'Old(i)))));


   procedure repe32_cmpsb with
     Global => (In_Out => (XSI, XDI, XCX, ZeroFlag, CarryFlag),
                Input  => Memory),
     Post => ((ECX = 0) or (not ZeroFlag));

end X86;



