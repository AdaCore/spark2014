------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--          Copyright (C) 2012-2014, Free Software Foundation, Inc.         --
------------------------------------------------------------------------------

with AIP.Config;
with AIP.Support;

package body AIP.Buffers.Common is

   --------------------
   -- Is_Data_Buffer --
   --------------------

   function Is_Data_Buffer (Buf : Buffers.Buffer_Id) return Boolean is
   begin
      --  Decision between data buffer and no-data buffer should not apply to
      --  null buffer, which is both
      Support.Verify (Buf /= NOBUF);

      return Buf <= Config.Data_Buffer_Num;
   end Is_Data_Buffer;

end AIP.Buffers.Common;
