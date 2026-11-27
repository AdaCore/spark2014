--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--  Extracted and modified from BWT for this regression test.
--  Upstream repository: https://github.com/kanigsson/BWT
--  Upstream commit: 6de077aae657ca6057fb26056bb71b10a676f96f
--  See LICENSE.

package BWT
  with SPARK_Mode
is
   pragma Elaborate_Body;

   --  Reference implementation: byte strings, normalized to a first index of 1.
   --  The bound keeps arithmetic within Integer, with room for the 4 * N
   --  comparison horizons; no byte is reserved as a sentinel.
   Max_Length : constant := 2**24;

   function Supported (S : String) return Boolean
   is (S'First = 1 and then S'Length <= Max_Length);

   --  The vocabulary of the specifications below. It lives here, not in a
   --  child, because the encoders' postconditions cannot name a child's
   --  declarations. A rotation reads the factor S (First .. First + Length - 1)
   --  periodically, starting at Offset.
   type Rotation is record
      First  : Positive := 1;
      Length : Positive := 1;
      Offset : Natural := 0;
   end record;
   type Table is array (Positive range <>) of Rotation;
private

end BWT;
