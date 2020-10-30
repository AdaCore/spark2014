pragma Ada_2020;

with Interfaces;
with Ada.Numerics.Big_Numbers.Big_Integers;
with Ada.Numerics.Big_Numbers.Big_Reals;

package Convert is

   use Interfaces;
   use Ada.Numerics.Big_Numbers.Big_Integers;
   use Ada.Numerics.Big_Numbers.Big_Reals;

   subtype Binary32 is Interfaces.IEEE_Float_32;

   subtype Unsigned_64 is Interfaces.Unsigned_64;
   subtype Integer_64 is Interfaces.Integer_64;
   subtype Unsigned_32 is Interfaces.Unsigned_32;
   subtype Integer_32 is Interfaces.Integer_32;

   package Uns_Conv is new Unsigned_Conversions (Unsigned_64);
   function BI (Arg : Unsigned_64) return Valid_Big_Integer
     renames Uns_Conv.To_Big_Integer;

   subtype Unsigned_128 is Interfaces.Unsigned_128;
   package Uns_Conv128 is new Unsigned_Conversions (Unsigned_128);
   function BI (Arg : Unsigned_128) return Valid_Big_Integer
     renames Uns_Conv128.To_Big_Integer;

   Representable_Seq_Last : constant := 2**24;
   --  Last 64-bit unsigned value of the contiguous sequence representable as
   --  a 32-bit float.

   Last_Float_As_Uns64 : constant Binary32 := Binary32'Pred (2.0**64);
   --  Last 32-bit float representable as a 64-bit unsigned

   --  Returns True iff F is the correct rounding between Low and Hi of value V
   function Correct_Rounding
     (V : Unsigned_64; F, Low, Hi : Binary32) return Boolean
   is
     (declare
        VR   : constant Big_Real := To_Big_Real (BI(V));
        LowR : constant Big_Real := To_Big_Real (BI(Unsigned_64(Low)));
        HiR  : constant Big_Real :=
          (if Hi = 2.0**64 then To_Big_Real (BI(Unsigned_128'(2**64)))
           else To_Big_Real (BI(Unsigned_64(Hi))));
      begin
        Hi = Binary32'Succ (Low)
        and then F in Low | Hi
        and then VR >= LowR
        and then VR <= HiR
        and then (if F = Low then VR - LowR <= HiR - VR)
        and then (if F = Hi  then VR - LowR >= HiR - VR))
        --  The tie-to-even case is still missing above
   with Pre =>
     Low <= Last_Float_As_Uns64
       and then
     (Hi = 2.0**64 or else Hi <= Last_Float_As_Uns64);

   function Floatundisf (V : Unsigned_64) return Binary32 with
      Post =>
          (declare
             Res : constant Binary32 := Floatundisf'Result;
           begin
             (if V <= Representable_Seq_Last then
                Unsigned_64 (Res) = V
              elsif V >= Unsigned_64 (Last_Float_As_Uns64) then
                Correct_Rounding (V, Res,
                                  Low => Last_Float_As_Uns64,
                                  Hi  => 2.0**64)
              else
                (declare
                   ResU : constant Unsigned_64 := Unsigned_64 (Res);
                 begin
                   (if V < ResU then
                      Correct_Rounding (V, Res,
                                        Low => Binary32'Pred (Res),
                                        Hi  => Res)
                    elsif V > ResU then
                      Correct_Rounding (V, Res,
                                        Low => Res,
                                        Hi  => Binary32'Succ (Res))))));

end Convert;
