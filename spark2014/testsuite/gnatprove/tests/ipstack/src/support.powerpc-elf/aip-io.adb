------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--             Copyright (C) 2012, Free Software Foundation, Inc.           --
------------------------------------------------------------------------------

with System.Text_IO;

package body AIP.IO is

   Line : String (1 .. 1024);
   Last : Integer := 0;

   procedure Put (S : String) is
   begin
      for J in S'Range loop
         System.Text_IO.Put (S (J));
      end loop;
   end Put;

   procedure Put_Line (S : String) is
   begin
      Put (S & ASCII.LF);
   end Put_Line;

   function Line_Available return Boolean is
   begin
      if not System.Text_IO.Is_Rx_Ready then
         return False;
      end if;
      Last := Last + 1;
      Line (Last) := System.Text_IO.Get;
      return Line (Last) = ASCII.LF;
   end Line_Available;

   function Get return String is
      R_Last : constant Integer := Last;
   begin
      Last := 0;
      return Line (1 .. R_Last - 1);
   end Get;

end AIP.IO;
