------------------------------------------------------------------------------
--                                                                          --
--                        SPARK LIBRARY COMPONENTS                          --
--                                                                          --
--                               R A N D O M                                --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                       Copyright (C) 2016, Altran UK Limited              --
--                                                                          --
-- SPARK is free software;  you can  redistribute it and/or modify it under --
-- terms of the  GNU General Public License as published  by the Free Soft- --
-- ware  Foundation;  either version 3,  or (at your option) any later ver- --
-- sion. SPARK is distributed in the hope that it will be useful, but WITH- --
-- OUT ANY WARRANTY;  without even the  implied warranty of MERCHANTABILITY --
-- or FITNESS FOR A PARTICULAR PURPOSE.                                     --
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

with Interfaces; use Interfaces;

package Random with
   SPARK_Mode,
   Pure
is

   type Generator is private;

   type Initialization_Vector is array (Natural range <>) of Unsigned_32;

   function Reset (Initiator : Unsigned_32) return Generator;
   --  Return a new generator initialized with the given seed.

   function Reset (Initiator : Initialization_Vector) return Generator
   with Pre => Initiator'First = Natural'First and Initiator'Length >= 1;
   --  Return a new generator initialized with the given seed.

   procedure Random (G     : in out Generator;
                     Value :    out Unsigned_32);
   --  Return the next number in the sequence.

private

   N : constant := 624;
   M : constant := 397;

   type State_Range is range 0 .. N - 1;

   type State_T is array (State_Range) of Unsigned_32;

   type Generator is record
      State : State_T;
      Index : State_Range;
   end record;

end Random;
