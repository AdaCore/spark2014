------------------------------------------------------------------------------
--                             M O D E L I N G                              --
--                                                                          --
--                     Copyright (C) 2011-2013, AdaCore                     --
--                                                                          --
-- This library is free software;  you can redistribute it and/or modify it --
-- under terms of the  GNU General Public License  as published by the Free --
-- Software  Foundation;  either version 3,  or (at your  option) any later --
-- version. This library is distributed in the hope that it will be useful, --
-- but WITHOUT ANY WARRANTY;  without even the implied warranty of MERCHAN- --
-- TABILITY or FITNESS FOR A PARTICULAR PURPOSE.                            --
--                                                                          --
-- As a special exception under Section 7 of GPL version 3, you are granted --
-- additional permissions described in the GCC Runtime Library Exception,   --
-- version 3.1, as published by the Free Software Foundation.               --
--                                                                          --
-- You should have received a copy of the GNU General Public License and    --
-- a copy of the GCC Runtime Library Exception along with this program;     --
-- see the files COPYING3 and COPYING.RUNTIME respectively.  If not, see    --
-- <http://www.gnu.org/licenses/>.                                          --
--                                                                          --
------------------------------------------------------------------------------

pragma SPARK_Mode;

package body Logger is

   -------------
   -- Content --
   -------------

   function Log_Content return Log_Array is
   begin
      if Event_Log.Empty then
         return Log_Array'(1 .. 0 => Make_Entry (0, 0, 0, 0.0, False));
      else
         declare
            Result : Log_Array (0 .. Log_Index (Log_Size - 1));
         begin
            if Event_Log.First <= Event_Log.Last then
               Result := Event_Log.Data (Event_Log.First .. Event_Log.Last);
            else
               Result :=
                 Event_Log.Data (Event_Log.First .. Log_Index'Last)
                   & Event_Log.Data (0 .. Event_Log.Last);
            end if;

            return Result;
         end;
      end if;
   end Log_Content;

end Logger;
