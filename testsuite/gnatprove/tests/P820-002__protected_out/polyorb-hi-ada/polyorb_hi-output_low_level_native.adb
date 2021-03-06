------------------------------------------------------------------------------
--                                                                          --
--                          PolyORB HI COMPONENTS                           --
--                                                                          --
--          P O L Y O R B _ H I . O U T P U T _ L O W _ L E V E L           --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--    Copyright (C) 2006-2009 Telecom ParisTech, 2010-2015 ESA & ISAE.      --
--                                                                          --
-- PolyORB-HI is free software; you can redistribute it and/or modify under --
-- terms of the  GNU General Public License as published  by the Free Soft- --
-- ware  Foundation;  either version 3,  or (at your option) any later ver- --
-- sion. PolyORB-HI is distributed in the hope that it will be useful, but  --
-- WITHOUT ANY WARRANTY; without even the implied warranty of               --
-- MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                     --
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
--              PolyORB-HI/Ada is maintained by the TASTE project           --
--                      (taste-users@lists.tuxfamily.org)                   --
--                                                                          --
------------------------------------------------------------------------------

with Interfaces.C;
with System;

package body PolyORB_HI.Output_Low_Level is

   ---------
   -- Put --
   ---------

   procedure C_Write
     (Fd  : Interfaces.C.int;
      P   : System.Address;
      Len : Interfaces.C.int);
   pragma Import (C, C_Write, "write");

   procedure Put (S : String)
     with SPARK_Mode => Off
     --  SPARK_Mode is distabled because of the Address attribute
   is
   begin
      C_Write (2, S (S'First)'Address, S'Length);
      --  2 is standard error

   end Put;

   --------------
   -- New_Line --
   --------------

   procedure New_Line is
      S : constant String := (1 => Character'Val (10));

   begin
      Put (S);
   end New_Line;

end PolyORB_HI.Output_Low_Level;
