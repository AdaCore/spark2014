------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--             Copyright (C) 2010, Free Software Foundation, Inc.           --
------------------------------------------------------------------------------

with AIP.Conversions;

package body AIP.Checksum is

   type M16_T_Array is array (Natural range <>) of M16_T;

   --------------
   -- Checksum --
   --------------

   function Checksum
     (Packet  : System.Address;
      Length  : Natural;
      Initial : M16_T := 0) return M16_T
   is
      Data   : M16_T_Array (1 .. Length / 2);
      for Data'Address use Packet;
      pragma Import (Ada, Data);

      Result : M32_T := M32_T (Initial);

      --  Assumption: Packet is aligned on a 16 bit boundary

   begin
      --  Sum over even bytes

      for J in Data'Range loop
         Result := Result + M32_T (Data (J));
      end loop;

      --  Account for remaining byte

      if Length mod 2 /= 0 then
         declare
            Remain : M8_T;
            for Remain'Address use Conversions.Ofs (Packet, Length - 1);
            pragma Import (Ada, Remain);
         begin
            Result := Result + M32_T (Remain) * 2 ** 8;
         end;
      end if;

      --  Wrap 1's complement 16-bit sum

      while Result >= 2 ** 16 loop
         Result := (Result and 16#ffff#) + (Result / 2**16);
      end loop;

      pragma Warnings (Off);
      --  Condition is constant for a given platform
      if AIP_Constants.Default_Bit_Order
           /= AIP_Constants.Network_Bit_Order
      then
         pragma Warnings (On);

         --  All computations above have been made in host order

         Result := (Result and 16#ff00#) / 2**8 + (Result and 16#ff#) * 2**8;
      end if;

      return M16_T (Result);
   end Checksum;

end AIP.Checksum;
