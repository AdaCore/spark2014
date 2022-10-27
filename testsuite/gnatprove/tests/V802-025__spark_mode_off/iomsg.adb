package body Iomsg is

   use Interfaces;

   function "and"
     (L, R : Extended_Flags_T)
      return Extended_Flags_T is
     (Extended_Flags_T (Unsigned_32 (L) and Unsigned_32 (R)));
end;
