------------------------------------------------------------------------------
--                                                                          --
--                          PolyORB HI COMPONENTS                           --
--                                                                          --
--                    P R O D U C E R _ C O N S U M E R                     --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--       Copyright (C) 2009 Telecom ParisTech, 2010-2015 ESA & ISAE.        --
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

--  $Id: producer_consumer.adb 6274 2009-03-25 19:56:54Z lasnier $

with PolyORB_HI.Output;
with PolyORB_HI_Generated.Deployment;

package body Producer_Consumer is

   use PolyORB_HI.Output;
   use PolyORB_HI_Generated.Deployment;

   The_Data : Alpha_Type := 1;

   function Get_Node return String;
   --  Return the current node name

   --------------
   -- Get_Node --
   --------------

   function Get_Node return String is
   begin
      return Node_Type'Image (My_Node);
   end Get_Node;

   -----------------
   -- Produce_Spg --
   -----------------

   procedure Produce_Spg (Data_Source : out Alpha_Type) is
   begin
      Data_Source := The_Data;

      if The_Data > 1000 then
         The_Data := 1;
      end if;

      The_Data := The_Data + 1;

      Put_Line (Normal, Get_Node
                & ": produced "
                & Alpha_Type'Image (Data_Source));
   end Produce_Spg;

   -----------------
   -- Consume_Spg --
   -----------------

   procedure Consume_Spg (Data_Sink : Alpha_Type) is
   begin
      Put_Line (Normal, Get_Node
                & "                              : consumed "
                & Alpha_Type'Image (Data_Sink));
   end Consume_Spg;
end Producer_Consumer;
