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

-------------------------------------------------------------------------------
-- (C) Altran Praxis Limited
-- modified by Martin Carlisle to add Argument function
-------------------------------------------------------------------------------
--
-- The SPARK toolset is free software; you can redistribute it and/or modify it
-- under terms of the GNU General Public License as published by the Free
-- Software Foundation; either version 3, or (at your option) any later
-- version. The SPARK toolset is distributed in the hope that it will be
-- useful, but WITHOUT ANY WARRANTY; without even the implied warranty of
-- MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU General
-- Public License for more details. You should have received a copy of the GNU
-- General Public License distributed with the SPARK toolset; see file
-- COPYING3. If not, go to http://www.gnu.org/licenses for a complete copy of
-- the license.
--
--=============================================================================

-------------------------------------------------------------------------------
--                                                                           --
-- SPARK.Ada.Command_Line                                                    --
--                                                                           --
-- Description                                                               --
--   This is a binding to package Ada.Command_Line                           --
--                                                                           --
-- Language                                                                  --
--   Specification : SPARK                                                   --
--   Private Part  : SPARK                                                   --
--   Body          : Ada                                                     --
--                                                                           --
-- Runtime Requirements and Dependencies                                     --
--   Full Ada Runtime                                                        --
--                                                                           --
-- Verification                                                              --
--   N/A                                                                     --
--                                                                           --
-- Exceptions                                                                --
--   None                                                                    --
-------------------------------------------------------------------------------
with SPARK.Text_IO;

package SPARK_Ada_Command_Line
  with Abstract_State => State,
       Initializes    => State
is

   -- function Argument_Count return Natural;
   function Argument_Count return Natural
     with Global => State;

   procedure Create_File_From_Argument
     (Number : in     Natural;
      File   :    out SPARK.Text_IO.File_Type)
     with Global  => (Input => State),
          Depends => (File => (Number, State));

   type Exit_Status is new Integer;

   Success : constant Exit_Status;
   Failure : constant Exit_Status;

   procedure Exit_With_Status (Code : in Exit_Status)
     with Depends => (null => Code);

private
   Success : constant Exit_Status := 0;
   Failure : constant Exit_Status := 1;
end SPARK_Ada_Command_Line;
