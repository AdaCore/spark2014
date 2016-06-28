------------------------------------------------------------------------------
--                                                                          --
--                          PolyORB HI COMPONENTS                           --
--                                                                          --
--                                H E L L O                                 --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--    Copyright (C) 2008-2009 Telecom ParisTech, 2010-2015 ESA & ISAE.      --
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

--  $Id: hello.adb 6273 2009-03-25 17:36:51Z lasnier $

--  with PolyORB_HI.Output;

package body Hello is

   -----------------
   -- Hello_Spg_1 --
   -----------------

   procedure Hello_Spg_1 is
--      use PolyORB_HI.Output;

   begin
      null;
      --      Put_Line (Normal, "Hello! This is task ONE");
   end Hello_Spg_1;

   -----------------
   -- Hello_Spg_2 --
   -----------------

   procedure Hello_Spg_2 is
--      use PolyORB_HI.Output;

   begin
      null;
      --      Put_Line (Normal, "Hello! This is task TWO");
   end Hello_Spg_2;

end Hello;
