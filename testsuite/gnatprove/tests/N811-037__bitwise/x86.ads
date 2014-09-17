package X86
with SPARK_Mode
is
   type Unsigned_64 is mod 2**64;
   type Unsigned_8  is mod 256;

   CarryFlag        : Boolean     := false;

   RDX : Unsigned_64 := 0;

   function DL return Unsigned_8 with
     Global => (Input => RDX),
     Post => (DL'Result = Unsigned_8(RDX and 16#00000000000000FF#));

   procedure Write_DL(Val : in Unsigned_8) with
     Global => (In_Out => RDX),
     Post => (RDX = ((RDX'Old and 16#FFFFFFFFFFFFFF00#) or Unsigned_64(Val)));

   procedure setb_DL with
     Global => (Input => CarryFlag, In_Out => RDX),
     Post => ((if (CarryFlag) then (DL = 1)) and
                (if (not CarryFlag) then (DL = 0)));
end X86;



