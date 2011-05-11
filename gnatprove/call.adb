------------------------------------------------------------------------------
--                                                                          --
--                            GNATPROVE COMPONENTS                          --
--                                                                          --
--                                 C A L L                                  --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                       Copyright (C) 2010-2011, AdaCore                   --
--                                                                          --
-- gnatprove is  free  software;  you can redistribute it and/or modify it  --
-- under terms of the  GNU General Public License as published  by the Free --
-- Software Foundation;  either version  2,  or  (at your option) any later --
-- version. gnatprove is distributed in the hope that it will  be  useful,  --
-- but WITHOUT ANY WARRANTY; without even the implied warranty of MERCHAN-  --
-- TABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU General Public --
-- License  for more details. You  should  have  received a copy of the GNU --
-- General Public License  distributed with GNAT; see file COPYING. If not, --
-- write to the Free Software Foundation,  51 Franklin Street, Fifth Floor, --
-- Boston,                                                                  --
--                                                                          --
-- gnatprove is maintained by AdaCore (http://www.adacore.com)              --
--                                                                          --
------------------------------------------------------------------------------

with Ada.Text_IO;
with GNAT.Expect;       use GNAT.Expect;

package body Call is

   ------------------------
   -- Abort_With_Message --
   ------------------------

   procedure Abort_With_Message (Msg : String) is
   begin
      Ada.Text_IO.Put_Line (Ada.Text_IO.Standard_Error, Msg);
      GNAT.OS_Lib.OS_Exit (1);
   end Abort_With_Message;

   --------------------------
   -- Call_Exit_On_Failure --
   --------------------------

   procedure Call_Exit_On_Failure
     (Command   : String;
      Arguments : Argument_List;
      Verbose   : Boolean := False)
   is
      Status : aliased Integer;

      procedure Print_Command_Line;
      --  print the command line for debug purposes

      ------------------------
      -- Print_Command_Line --
      ------------------------

      procedure Print_Command_Line is
      begin
         Ada.Text_IO.Put (Command);

         for Index in Arguments'Range loop
            declare
               S : constant String_Access := Arguments (Index);
            begin
               Ada.Text_IO.Put (" ");
               Ada.Text_IO.Put (S.all);
            end;
         end loop;
      end Print_Command_Line;

   begin
      if Verbose then
         Print_Command_Line;
         Ada.Text_IO.Put_Line ("");
      end if;

      declare
         S : constant String :=
            GNAT.Expect.Get_Command_Output
              (Command   => Command,
               Arguments => Arguments,
               Input     => "",
               Status    => Status'Access,
               Err_To_Out => True);
      begin
         if Verbose or else Status /= 0 then
            Ada.Text_IO.Put (S);
            if Status /= 0 then
               Print_Command_Line;
               Ada.Text_IO.Put_Line (" failed.");
               GNAT.OS_Lib.OS_Exit (1);
            else
               Ada.Text_IO.Put_Line ("");
            end if;
         end if;

         for Index in Arguments'Range loop
            declare
               S : String_Access := Arguments (Index);
            begin
               Free (S);
            end;
         end loop;
      end;
   end Call_Exit_On_Failure;

end Call;
