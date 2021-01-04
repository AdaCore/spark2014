------------------------------------------------------------------------------
--                                                                          --
--                           GNAT2WHY COMPONENTS                            --
--                                                                          --
--                   F L O W . D Y N A M I C _ M E M O R Y                  --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                Copyright (C) 2019-2021, Altran UK Limited                --
--                                                                          --
-- gnat2why is  free  software;  you can redistribute  it and/or  modify it --
-- under terms of the  GNU General Public License as published  by the Free --
-- Software  Foundation;  either version 3,  or (at your option)  any later --
-- version.  gnat2why is distributed  in the hope that  it will be  useful, --
-- but WITHOUT ANY WARRANTY; without even the implied warranty of  MERCHAN- --
-- TABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU General Public --
-- License for  more details.  You should have  received  a copy of the GNU --
-- General  Public License  distributed with  gnat2why;  see file COPYING3. --
-- If not,  go to  http://www.gnu.org/licenses  for a complete  copy of the --
-- license.                                                                 --
--                                                                          --
------------------------------------------------------------------------------

package Flow.Dynamic_Memory is

   procedure Create_Heap_State
   with Post => Present (Heap_State);
   --  Finds the entity of a predefined abstract state that represents memory
   --  (de)allocation if its enclosing package has been WITH-ed from the
   --  current complication unit; otherwise, creates an artificial entity for
   --  this abstract state.

   function Heap_State return Entity_Id
   with Post => Ekind (Heap_State'Result) = E_Abstract_State;
   --  Returns the abstract state that represent memory (de)allocation

   function Is_Heap_State (E : Entity_Id) return Boolean
   with Post => (if Is_Heap_State'Result then Ekind (E) = E_Abstract_State);
   --  Returns True iff E is the heap state (for allocations and deallocations
   --  in code in SPARK).

end Flow.Dynamic_Memory;
