-- C3900051.A
--
--                             Grant of Unlimited Rights
--
--     Under contracts F33600-87-D-0337, F33600-84-D-0280, MDA903-79-C-0687,
--     F08630-91-C-0015, and DCA100-97-D-0025, the U.S. Government obtained
--     unlimited rights in the software and documentation contained herein.
--     Unlimited rights are defined in DFAR 252.227-7013(a)(19).  By making
--     this public release, the Government intends to confer upon all
--     recipients unlimited rights  equal to those held by the Government.
--     These rights include rights to use, duplicate, release or disclose the
--     released technical data and computer software in whole or in part, in
--     any manner and for any purpose whatsoever, and to have or permit others
--     to do so.
--
--                                    DISCLAIMER
--
--     ALL MATERIALS OR INFORMATION HEREIN RELEASED, MADE AVAILABLE OR
--     DISCLOSED ARE AS IS.  THE GOVERNMENT MAKES NO EXPRESS OR IMPLIED
--     WARRANTY AS TO ANY MATTER WHATSOEVER, INCLUDING THE CONDITIONS OF THE
--     SOFTWARE, DOCUMENTATION OR OTHER INFORMATION RELEASED, MADE AVAILABLE
--     OR DISCLOSED, OR THE OWNERSHIP, MERCHANTABILITY, OR FITNESS FOR A
--     PARTICULAR PURPOSE OF SAID MATERIAL.
--*
--
-- OBJECTIVE:
--      See C3900053.AM.
--
-- TEST DESCRIPTION:
--      See C3900053.AM.
--
-- TEST FILES:
--      This test consists of the following files:
--
--         C3900050.A
--      => C3900051.A
--         C3900052.A
--         C3900053.AM
--
-- CHANGE HISTORY:
--      06 Dec 94   SAIC    ACVC 2.0
--      15 May 96   SAIC    ACVC 2.1: Modified prologue. Added pragma Elaborate
--                          for Ada.Calendar.
--
--!

with C3900050;       -- Alert system abstraction.
package C3900051 is  -- Extended alert system abstraction.


   type Low_Alert_Type is new C3900050.Alert_Type
     with private;                                      -- Private extension of
                                                        -- root tagged type.

   -- Inherits procedure Display from Alert_Type.

   procedure Handle (LA : in out Low_Alert_Type);       -- Override parent's
                                                        -- primitive subprog.

   procedure Set_Level (LA : in out Low_Alert_Type;     -- To be inherited by
                        L  : in     Integer);           -- all derivatives.


   -- The following functions are needed to verify the values of the
   -- extension's private components.

   function Get_Level (LA: Low_Alert_Type) return Integer;

   function Initial_Values_Okay (LA : in Low_Alert_Type)
     return Boolean;                                    -- Override parent's
                                                        -- primitive subprog.

   function Bad_Final_Values (LA : in Low_Alert_Type)   -- Override parent's
     return Boolean;                                    -- primitive subprog.


private

   type Low_Alert_Type is new C3900050.Alert_Type with record
      Level : Integer := 0;
   end record;

end C3900051;
