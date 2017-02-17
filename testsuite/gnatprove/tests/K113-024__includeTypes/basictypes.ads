package BasicTypes is

   type Unsigned32T is range 0 .. 2**32 - 1;
   for Unsigned32T'Size use 32;

   type Signed32T is range - (2**31) .. 2**31 - 1;
   for Signed32T'Size use 32;

   type ByteT is range 0..255;
   for ByteT'Size use 8;

   type PresenceT is (Present, Absent);

end BasicTypes;
