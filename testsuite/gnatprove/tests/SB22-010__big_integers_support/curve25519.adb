--  Copyright 2008, Google Inc. All rights reserved.
--
--  Redistribution and use in source and binary forms, with or without
--  modification, are permitted provided that the following conditions are
--  met:
--
--  *  Redistributions of source code must retain the above copyright
--     notice, this list of conditions and the following disclaimer.
--  *  Redistributions in binary form must reproduce the above copyright
--     notice, this list of conditions and the following disclaimer in the
--     documentation and/or other materials provided with the distribution.
--  *  Neither the name of Google Inc. nor the names of its contributors may
--     be used to endorse or promote products derived from this software
--     without specific prior written permission.
--
--  THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS
--  IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED
--  TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A
--  PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER
--  OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,
--  EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO,
--  PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR
--  PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
--  LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
--  NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
--  SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.


package body Curve25519 with
  SPARK_Mode
is

   function Add (X, Y : Integer_255) return Integer_255 is
      Sum : Integer_255 := (others => 0);
      X_256, Y_256, Sum_256 : Big_Integer := Zero with Ghost;
   begin
      for J in Sum'Range loop

         Sum (J) := X (J) + Y (J);

         pragma Loop_Invariant (for all K in 0 .. J =>
                                  Sum (K) = X (K) + Y (K));

      end loop;

      for J in Sum'Range loop

         X_256 := X_256 + (+X (J)) * Conversion_Array (J);
         Y_256 := Y_256 + (+Y (J)) * Conversion_Array (J);
         Sum_256 := Sum_256 + (+Sum (J)) * Conversion_Array (J);

         pragma Assert ((+X (J)) * Conversion_Array (J) +
                          (+Y (J)) * Conversion_Array (J) =
                        (+ (X (J) + Y (J))) * Conversion_Array (J));
         pragma Assert (X (J) + Y (J) = Sum (J));
         pragma Assert ((+ (X (J) + Y (J))) * Conversion_Array (J)
                        = (+Sum (J)) * Conversion_Array (J));

         pragma Loop_Invariant (X_256 = Partial_Conversion (X, J));
         pragma Loop_Invariant (Y_256 = Partial_Conversion (Y, J));
         pragma Loop_Invariant (Sum_256 = Partial_Conversion (Sum, J));
         pragma Loop_Invariant (Partial_Conversion (Sum, J) =
                                  Partial_Conversion (X, J) +
                                  Partial_Conversion (Y, J));
      end loop;

      return Sum;
   end Add;

end Curve25519;
