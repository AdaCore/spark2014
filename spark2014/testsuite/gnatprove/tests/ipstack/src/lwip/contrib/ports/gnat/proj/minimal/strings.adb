------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--             Copyright (C) 2010, Free Software Foundation, Inc.           --
------------------------------------------------------------------------------

with Ada.Unchecked_Conversion;
with System.Storage_Elements; use System.Storage_Elements;

package body Strings is
   use type Interfaces.C.size_t;
   use type Interfaces.C.char;

   subtype mem is Interfaces.C.char_array (Interfaces.C.size_t);
   type memptr is access all mem;
   function to_memptr is new Ada.Unchecked_Conversion (System.Address, memptr);

   function strlen (S : System.Address) return Interfaces.C.size_t is
      s_p  : constant memptr := to_memptr (S);
      Len  : Interfaces.C.size_t := 0;
   begin
      while s_p (s_p'First + Len) /= Interfaces.C.NUL loop
         Len := Len + 1;
      end loop;
      return Len;
   end strlen;

   function strncpy
     (Dest : System.Address;
      Src  : System.Address;
      N    : Interfaces.C.size_t) return System.Address
   is
      dest_p : constant memptr := to_memptr (Dest);
      src_p  : constant memptr := to_memptr (Src);

      Index : Interfaces.C.size_t := Interfaces.C.size_t'First;
   begin
      if N > 0 then
         while src_p (Index) /= Interfaces.C.NUL
                  and then Index - Interfaces.C.size_t'First < N - 1
         loop
            dest_p (Index) := src_p (Index);
            Index := Index + 1;
         end loop;

         while Index < N loop
            dest_p (Index) := Interfaces.C.NUL;
         end loop;
      end if;
      return dest;
   end strncpy;

end Strings;
