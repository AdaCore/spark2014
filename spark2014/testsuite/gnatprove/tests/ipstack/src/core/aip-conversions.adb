------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--             Copyright (C) 2010, Free Software Foundation, Inc.           --
------------------------------------------------------------------------------

--  Internal conversion services for AIP

with Ada.Unchecked_Conversion;
with System.Storage_Elements;

package body AIP.Conversions is

   ---------
   -- Ofs --
   ---------

   function Ofs (A : System.Address; Offset : Integer) return System.Address is
      use type System.Storage_Elements.Storage_Offset;
   begin
      return A + System.Storage_Elements.Storage_Offset (Offset);
   end Ofs;

   ----------
   -- Diff --
   ----------

   function Diff (A : System.Address; B : System.Address) return Integer is
      use type System.Storage_Elements.Storage_Offset;
   begin
      return Integer (A - B);
   end Diff;

   ------------
   -- Memcpy --
   ------------

   procedure Memcpy
     (Dst : System.Address;
      Src : System.Address;
      Len : Integer)
   is
      type mem is array (Integer) of Character;
      type memptr is access mem;
      function to_memptr is
        new Ada.Unchecked_Conversion (System.Address, memptr);
      dst_p : constant memptr := to_memptr (Dst);
      src_p : constant memptr := to_memptr (Src);
   begin
      if Len > 0 then
         for J in 0 .. Len - 1 loop
            dst_p (J) := src_p (J);
         end loop;
      end if;
   end Memcpy;

end AIP.Conversions;
