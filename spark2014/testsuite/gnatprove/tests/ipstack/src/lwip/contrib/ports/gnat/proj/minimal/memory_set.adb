------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--             Copyright (C) 2010, Free Software Foundation, Inc.           --
------------------------------------------------------------------------------

with Ada.Unchecked_Conversion;

package body Memory_Set is

   ------------
   -- memset --
   ------------

   function Memset (M : Address; C : int; Size : size_t) return Address is
      subtype Mem_Array is char_array (size_t);
      type Mem_Ptr is access Mem_Array;

      function To_Memptr is
         new Ada.Unchecked_Conversion (Address, Mem_Ptr);

      Dest : constant Mem_Ptr := To_Memptr (M);

   begin
      if Size > 0 then
         for J in 0 .. Size - 1 loop
            Dest (J) := char'Val (C);
         end loop;
      end if;

      return M;
   end Memset;

end Memory_Set;
