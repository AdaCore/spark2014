------------------------------------------------------------------------------
--                                                                          --
--                        SPARK LIBRARY COMPONENTS                          --
--                                                                          --
--                                S P A R K                                 --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                Copyright (C) 2019-2021, Altran UK Limited                --
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

--  This unit provides an abstract state that is implicitly referenced when
--  (de)allocating dynamic memory with "new" and with instances of
--  Ada.Unchecked_Deallocation, respectively. This abstract state is meant to
--  be used in explicit Global and Depends contract (and their refined
--  variants).

package SPARK.Heap with
   SPARK_Mode,
   Abstract_State => (Dynamic_Memory with External => Async_Writers)
is
   pragma Elaborate_Body;
end SPARK.Heap;
