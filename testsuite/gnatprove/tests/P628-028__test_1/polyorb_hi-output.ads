------------------------------------------------------------------------------
--                                                                          --
--                          PolyORB HI COMPONENTS                           --
--                                                                          --
--                    P O L Y O R B _ H I . O U T P U T                     --
--                                                                          --
--                                 S p e c                                  --
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

--  Debug facility of PolyORB HI

with Ada.Real_Time;

with PolyORB_HI.Epoch;
with PolyORB_HI.Streams;

package PolyORB_HI.Output
  with Abstract_State => (Elaborated_Variables with Synchronous,
                          External => (Effective_Reads,
                                       Effective_Writes,
                                       Async_Writers,
                                       Async_Readers)),
       Initializes => Elaborated_Variables
is
   pragma Elaborate_Body;

   use PolyORB_HI.Streams;

   type Verbosity is
     (Verbose,
      --  Developer interest only, should never be displayed
      --  in a production environment.

      Normal,
      --  Informational message indicating progress of normal
      --  operation.

      Error
      --  Indication that an abnormal condition has been identified
      );

   Current_Mode : constant Verbosity := Normal;
   --  Curent debug level

   procedure Put_Line (Mode : in Verbosity := Normal; Text : in String);
   --  Display Text iff Mode is greater than Current_Mode. This
   --  routine is thread-safe.

   procedure Put (Mode : in Verbosity := Normal; Text : in String);
   --  Display Text iff Mode is greater than Current_Mode. This
   --  routine is thread-safe.

   procedure Put_Line (Text : in String)
     with Global => (In_Out => Elaborated_Variables,
                     Input => (Ada.Real_Time.Clock_Time,
                               Epoch.Elaborated_Variables));
   --  Same as above, but always displays the message

   procedure Put (Text : in String)
     with Global => (In_Out => Elaborated_Variables,
                    Input => (Ada.Real_Time.Clock_Time,
                              Epoch.Elaborated_Variables));
   --  Same as above but always displays the message

   procedure Dump (Stream : Stream_Element_Array; Mode : Verbosity := Verbose)
     with Global => (In_Out => Elaborated_Variables,
                     Input => (Ada.Real_Time.Clock_Time,
                               Epoch.Elaborated_Variables));
   --  Dump the content of Stream in an hexadecimal format

   function "+" (S1 : String; S2 : String) return String
     with Pre => (S1'Length <= 255 and S2'Length <= 255);
   --  Simple helper function to concatenate two strings

end PolyORB_HI.Output;
