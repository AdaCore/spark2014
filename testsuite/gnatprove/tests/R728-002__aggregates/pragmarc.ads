-- PragmAda Reusable Component (PragmARC)
-- Copyright (C) 2002 by PragmAda Software Engineering.  All rights reserved.
-- **************************************************************************
--
-- Root package for PragmAda Reusable Components
--
-- History:
-- 2002 May 01     J. Carter          V1.1--Added Too_Short
-- 2000 May 01     J. Carter          V1.0--Initial release
--
package PragmARC is
   pragma Pure;

   Empty : exception; -- Raised by components when an attempt is made to access data in an empty structure

   Full : exception; -- Raised by bounded components when an attempt is made to add data to a full structure

   Storage_Exhausted : exception;
   -- Raised by unbounded components when there is not enough memory available for an operation

   Too_Short : exception; -- Raised by Assign for bounded components if not enough room
end PragmARC;
--
-- This is free software; you can redistribute it and/or modify it under
-- terms of the GNU General Public License as published by the Free Software
-- Foundation; either version 2, or (at your option) any later version.
-- This software is distributed in the hope that it will be useful, but WITH
-- OUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
-- or FITNESS FOR A PARTICULAR PURPOSE. See the GNU General Public License
-- for more details. Free Software Foundation, 59 Temple Place - Suite
-- 330, Boston, MA 02111-1307, USA.
--
-- As a special exception, if other files instantiate generics from this
-- unit, or you link this unit with other files to produce an executable,
-- this unit does not by itself cause the resulting executable to be
-- covered by the GNU General Public License. This exception does not
-- however invalidate any other reasons why the executable file might be
-- covered by the GNU Public License.