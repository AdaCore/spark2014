pragma Ada_2005;
pragma Style_Checks (Off);

with Interfaces.C; use Interfaces.C;
with Interfaces.C.Extensions;

package types is

   c_NULL : constant := (0);  --  types.h:45

   subtype uint8_t is unsigned_char;  -- types.h:32

   subtype uint16_t is unsigned_short;  -- types.h:33

   subtype uint32_t is unsigned;  -- types.h:34

   subtype uint64_t is Extensions.unsigned_long_long;  -- types.h:35

   subtype int8_t is signed_char;  -- types.h:37

   subtype int16_t is short;  -- types.h:38

   subtype int32_t is int;  -- types.h:39

   subtype int64_t is Long_Long_Integer;  -- types.h:40

   subtype size_t is unsigned;  -- types.h:42

   subtype intptr_t is unsigned_long;  -- types.h:43

end types;
