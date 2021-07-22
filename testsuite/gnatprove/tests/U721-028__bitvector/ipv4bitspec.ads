pragma Ada_2022;
with Interfaces; use Interfaces;

package IpV4BitSpec
  with SPARK_Mode
is
  V4_MASK : constant Unsigned_128 := 16#ffff_ffff#;

  function IpV4BitsWellFormed(bv: Unsigned_128) return Boolean is
    ((bv and V4_MASK) = bv);

  type seqBv8 is array (Natural range <>) of Unsigned_8 with
    Predicate => seqBv8'First = 0;

  function Truncate8(br: Unsigned_128) return Unsigned_128 is
    (br and 16#ff#);

  function IpV4BitsToBytes(br: Unsigned_128) return seqBv8 is
    (declare
       b0 : constant Unsigned_8 := Unsigned_8 (Truncate8 (Shift_Right (br, 24)));
       b1 : constant Unsigned_8 := Unsigned_8 (Truncate8 (Shift_Right (br, 16)));
       b2 : constant Unsigned_8 := Unsigned_8 (Truncate8 (Shift_Right (br, 8)));
       b3 : constant Unsigned_8 := Unsigned_8 (Truncate8 (Shift_Right (br, 0)));
     begin (b0, b1, b2, b3));

  function IpV4BytesToBits(bytes: seqBv8) return Unsigned_128 is
    (declare
       b0 : constant Unsigned_128 := Shift_Left (Unsigned_128 (bytes (0)), 24);
       b1 : constant Unsigned_128 := Shift_Left (Unsigned_128 (bytes (1)), 16);
       b2 : constant Unsigned_128 := Shift_Left (Unsigned_128 (bytes (2)), 8);
       b3 : constant Unsigned_128 := Shift_Left (Unsigned_128 (bytes (3)), 0);
     begin (b0 or b1 or b2 or b3))
  with Pre => bytes'Length = 4,
    Post => IpV4BitsWellFormed(IpV4BytesToBits'Result);

 procedure IpV4BitsToBytesEq(bv: Unsigned_128) with
    Ghost,
    Pre => IpV4BitsWellFormed(bv),
    Post => IpV4BytesToBits(IpV4BitsToBytes(bv)) = bv;

  procedure IpV4BytesToBitsEq(bytes: seqBv8) with
    Ghost,
    Pre => bytes'Length = 4,
    Post => IpV4BitsToBytes(IpV4BytesToBits(bytes)) = bytes;

end IpV4BitSpec;
