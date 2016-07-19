package body Arithmetic
is
   type Unsigned_Byte is range 0..255;
   type Byte is range -128..127;

   function Halve_D (N: in Unsigned_Byte) return Unsigned_Byte
     with Post => Halve_D'Result = N / 2
   is
      R : Unsigned_Byte;
   begin
      for I in Unsigned_Byte range 0 .. Unsigned_Byte'Last / 2
      loop
         R := I;
         exit when R + R = N or (R + R) + 1 = N;
         pragma Loop_Invariant (R = I
                                  and N > R + R + 1
                                  and R in Unsigned_Byte);
      end loop;
      return R;
   end Halve_D;

end Arithmetic;
