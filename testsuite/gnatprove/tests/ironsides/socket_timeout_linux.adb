----------------------------------------------------------------
-- IRONSIDES - DNS SERVER
--
-- By: Martin C. Carlisle and Barry S. Fagin
--     Department of Computer Science
--     United States Air Force Academy
--
-- Modified by: Altran UK Limited
--
-- This is free software; you can redistribute it and/or
-- modify without restriction.  We do ask that you please keep
-- the original author information, and clearly indicate if the
-- software has been modified.
--
-- This software is distributed in the hope that it will be useful,
-- but WITHOUT ANY WARRANTY; without even the implied warranty
-- of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
----------------------------------------------------------------

with Gnat.Sockets.Thin;
with Interfaces;
with Interfaces.C;
with Ada.Unchecked_Conversion,
     Gnat.Sockets.Constants,
     Ada.Text_IO;

package body Socket_Timeout
  with SPARK_Mode => Off
is

   ------------------------
   -- Set_Socket_Timeout --
   ------------------------

   type Timeval_Unit is new Interfaces.C.int;
   pragma Convention (C, Timeval_Unit);

   type Timeval is record
      Tv_Sec  : Timeval_Unit;
      Tv_Usec : Timeval_Unit;
   end record;
   pragma Convention (C, Timeval);

   procedure Set_Socket_Timeout
     (Socket       : Socket_Type;
      Milliseconds : Natural)
   is
      Res : Interfaces.C.Int;
      function Convert is new Ada.Unchecked_Conversion
        (Socket_Type, Interfaces.C.Int);
      Time : timeval;
      use type Interfaces.C.Int;
   begin
      Time.tv_sec := timeval_unit(Milliseconds/1000);
      Time.tv_usec := timeval_unit((Milliseconds mod 1000)*1000);
      Res := Gnat.Sockets.Thin.C_Setsockopt
        (Convert (Socket),
         Gnat.Sockets.Constants.SOL_SOCKET,
         Gnat.Sockets.Constants.SO_RCVTIMEO,
         time'address, 8);
--      ada.text_io.put_line("set option: " &
--        Timeval_unit'image(Time.tv_sec) &
--        Timeval_unit'image(Time.tv_usec) &
--        Interfaces.C.Int'image(res) & integer'image(time'size/8));
      Res := Gnat.Sockets.Thin.C_Setsockopt
        (Convert (Socket),
         Gnat.Sockets.Constants.SOL_SOCKET,
         Gnat.Sockets.Constants.SO_SNDTIMEO,
         Time'Address, 8);
   end Set_Socket_Timeout;

end Socket_Timeout;
