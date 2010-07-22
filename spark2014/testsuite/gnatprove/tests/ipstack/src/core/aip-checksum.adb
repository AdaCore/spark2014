------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--             Copyright (C) 2010, Free Software Foundation, Inc.           --
------------------------------------------------------------------------------

with AIP.Conversions;

package body AIP.Checksum is

   type M16_T_Array is array (Natural range <>) of M16_T;

   ---------
   -- Sum --
   ---------

   function Sum
     (Packet  : System.Address;
      Length  : Natural;
      Initial : AIP.M16_T) return AIP.M16_T
   is
      Data   : M16_T_Array (1 .. Length / 2);
      for Data'Address use Packet;
      pragma Import (Ada, Data);

      --  Assumption: Packet is aligned on a 16 bit boundary

      Result : M32_T := M32_T (Initial);

      function Get_Byte (A : System.Address) return M8_T;
      --  Return byte at address A

      --------------
      -- Get_Byte --
      --------------

      function Get_Byte (A : System.Address) return M8_T is
         B : M8_T;
         for B'Address use A;
         pragma Import (Ada, B);
      begin
         return B;
      end Get_Byte;

   --  Start of processing for Checksum

   begin
      --  Sum over even bytes

      for J in Data'Range loop
         Result := Result + M32_T (Data (J));
      end loop;

      --  Account for remaining byte

      if Length mod 2 /= 0 then
         Result := Result +
           M32_T (Get_Byte (Conversions.Ofs (Packet, Length - 1))) * 2 ** 8;
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
   end Sum;

end AIP.Checksum;
