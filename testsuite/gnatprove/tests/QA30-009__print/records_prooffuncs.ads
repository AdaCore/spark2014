package Records_ProofFuncs
is
   type Unsigned_Byte is range 0 .. 255;

   type Apir1 is record
      A : Unsigned_Byte;
      B : Unsigned_Byte;
   end record;

   Null_Pair : constant Apir1 := Apir1'(A => 0,
                                        B => 0);

   function F_Of_Pair (P : in Apir1) return Boolean;
end Records_ProofFuncs;
