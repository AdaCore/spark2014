------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--             Copyright (C) 2010, Free Software Foundation, Inc.           --
------------------------------------------------------------------------------

--  This package provides general block copy mechanisms analgous to those
--  provided by the C routines memcpy and memmove allowing for copies with
--  and without possible overflow.

with System; use System;
with Interfaces.C; use Interfaces.C;

package Memory_Copy is
pragma Preelaborate;

   procedure memcpy (Dest : Address; Src : Address; N : size_t);
   pragma Export (C, memcpy, "memcpy");
   --  Copies N storage units from area starting at Src to area starting
   --  at Dest without any check for buffer overflow. The memory areas
   --  must not overlap, or the result of this call is undefined.

   procedure memmove (Dest : Address; Src : Address; N : size_t);
   pragma Export (C, memmove, "memmove");
   --  Copies N storage units from area starting at S2 to area starting
   --  at S1 without any check for buffer overflow. The difference between
   --  this memmove and memcpy is that with memmove, the storage areas may
   --  overlap (forwards or backwards) and the result is correct (i.e. it
   --  is as if S2 is first moved to a temporary area, and then this area
   --  is copied to S1 in a separate step).

end Memory_Copy;
