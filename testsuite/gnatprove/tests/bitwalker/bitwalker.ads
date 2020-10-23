with Interfaces; use Interfaces;
with BitTypes;   use BitTypes;
with BitSpec;    use BitSpec;
with Bvext;      use Bvext;

package Bitwalker with
SPARK_Mode
is
   function PeekBit8 (Byte : Unsigned_8; Left : Natural) return Boolean
   with
     Pre  => Left < 8,
     Post => PeekBit8'Result = Nth (Byte, 7 - Left);

   function PeekBit8Array (Addr : Byte_Sequence; Left : Natural) return Boolean is
     (PeekBit8 (Addr (Left / 8), Left rem 8))
   with
     Pre    => Addr'First = 0 and then
               Left < 8 * Addr'Length,
     Global => null,
     Post   => PeekBit8Array'Result = Nth8_Stream (Addr, Left);

   function PokeBit64
      (Value : Unsigned_64;
       Left  : Natural;
       Flag  : Boolean) return Unsigned_64
   with
     Pre    => Left < 64,
     Global => null,
     Post   => (for all I in Natural range 0 .. 63 =>
                  (if I /= 63 - Left then
                         Nth (PokeBit64'Result, I) = Nth (Value, I)))
               and
                 (Flag = Nth (PokeBit64'Result, 63 - Left));

   function Peek
     (Start, Length : Natural;
      Addr          : Byte_Sequence) return Unsigned_64
     with
       Pre            => Addr'First = 0 and then
                         Length <= 64 and then
                         Start + Length <= Natural'Last and then
                         8 * Addr'Length <= Natural'Last,
       Global         => null,
       Contract_Cases =>
         (Start + Length > 8 * Addr'Length =>
            Peek'Result = 0,
         (Start + Length <= 8 * Addr'Length) =>
           (for all I in 0 .. Length - 1 =>
                    Nth8_Stream (Addr, Start + Length - I - 1)
                  = Nth (Peek'Result, I))
          and then
           (for all I in Length .. 63 => not Nth (Peek'Result, I)));

   function PeekBit64 (Value : Unsigned_64;
                       Left  : Natural)
                       return Boolean
   is
     ((Value and Shift_Left (1, 63 - Left)) /= 0)
   with
       Pre  => Left < 64,
       Post => PeekBit64'Result = Nth (Value, (63 - Left));

   function PokeBit8 (Byte : Unsigned_8;
                      Left : Natural;
                      Flag : Boolean)
                      return Unsigned_8
     with
       Pre  => Left < 8,
       Post =>
         (for all I in 0 .. 7 =>
            (if I /= 7 - Left then
              Nth (PokeBit8'Result, I) = Nth (Byte, I))) and then
         Nth (PokeBit8'Result, 7 - Left) = Flag;

   procedure PokeBit8Array (Addr : in out Byte_Sequence;
                            Left : Natural;
                            Flag : Boolean)
     with
       Pre  => Addr'First = 0 and then Left < 8 * Addr'Length,
       Post =>
         (for all I in 0 .. 8 * Addr'Length - 1 =>
            (if I /= Left then
                     Nth8_Stream (Addr, I) = Nth8_Stream (Addr'Old, I)))
          and then
            Nth8_Stream (Addr, Left) = Flag;

   procedure Poke (Start, Len : Natural;
                   Addr       : in out Byte_Sequence;
                   Value      : Unsigned_64;
                   Result     : out Integer)
     with
       Pre  => Addr'First = 0 and then
               8 * Addr'Length <= Natural'Last and then
               Start + Len < Natural'Last and then
               Len in 0 .. 63,
       Post => (Result in -2 .. 0) and then
               ((Result = -1) = (Start + Len > 8 * Addr'Length)) and then
               ((Result = -2) = (MaxValue (Len) <= Value
                                 and Start + Len <= 8 * Addr'Length))
             and then
               ((Result = 0) = (MaxValue (Len) > Value
                                and Start + Len <= 8 * Addr'Length))
             and then
               (if Result = 0 then
                  (for all I in 0 .. Start - 1 =>
                         Nth8_Stream (Addr'Old, I) = Nth8_Stream (Addr, I)))
             and then
               (if Result = 0 then
                  (for all I in Start .. Start + Len - 1 =>
                         Nth8_Stream (Addr, I)
                   = Nth (Value, Len - I - 1 + Start )))
             and then
               (if Result = 0 then
                  (for all I in Start + Len .. 8 * Addr'Length - 1=>
                         Nth8_Stream (Addr, I)
                   = Nth8_Stream (Addr'Old ,I)));

   procedure Lemma_Less_Than_Max (X : Unsigned_64; Len : Integer)
     with
       Ghost,
       Pre  => Len in 0 .. 63 and then
               (for all I in Len .. 63 => not Nth (X, I)),
       Post => X < MaxValue (Len);

   procedure Lemma_Less_Than_Max2 (X : Unsigned_64; Len : Integer)
     with
       Ghost,
       Pre  => Len in 0 .. 63 and then X < MaxValue (Len),
       Post => (for all I in Len .. 63 => not Nth (X, I));

   procedure Lemma_Nth_Eq (X, Y : Unsigned_64)
     with
       Ghost,
       Pre  => (for all I in 0 .. 63 => Nth (X, I) = Nth (Y, I)),
       Post => X = Y;

   procedure PeekThenPoke (Start, Len : Natural;
                           Addr       : in out Byte_Sequence;
                           Result     : out Integer)
     with
       Ghost,
       Pre =>
         Addr'First = 0 and then
         8 * Addr'Length <= Natural'Last and then
         Len in 0 .. 63 and then
         Start + Len <= 8 * Addr'Length,
       Post =>
           Result = 0 and then
           (for all I in 0 .. 8 * Addr'Length - 1 =>
              Nth8_Stream (Addr, I) = Nth8_Stream (Addr'Old, I));

   procedure PokeThenPeek (Start, Len : Natural;
                           Addr : in out Byte_Sequence;
                           Value : Unsigned_64;
                           Result : out Unsigned_64)
     with
       Ghost,
       Pre =>
         Addr'First = 0 and then
         8 * Addr'Length < Natural'Last and then
         Len in 0 .. 63 and then
         Start + Len <= Addr'Length and then
         Value < MaxValue (Len),
       Post =>
          Result = Value;

end Bitwalker;
