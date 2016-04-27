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

with Gnat.Sockets.Thin,
     Interfaces,
     Interfaces.C,
     Ada.Unchecked_Conversion,
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
      Time : integer;
      use type Interfaces.C.Int;
   begin
      Time := Milliseconds;
      Res := Gnat.Sockets.Thin.C_Setsockopt
        (Convert (Socket),
         Gnat.Sockets.Constants.SOL_SOCKET,
         Gnat.Sockets.Constants.SO_RCVTIMEO,
         Time'address, 4);
      --      ada.text_io.put_line("set option: " & C.Int'image(res) &
      --                           integer'image(time'size/8));
      Res := Gnat.Sockets.Thin.C_Setsockopt
        (Convert (Socket),
         Gnat.Sockets.Constants.SOL_SOCKET,
         Gnat.Sockets.Constants.SO_SNDTIMEO,
         Time'Address, 4);
      --      ada.text_io.put_line("set option: " & C.Int'image(res));
   end Set_Socket_Timeout;

end Socket_Timeout;
