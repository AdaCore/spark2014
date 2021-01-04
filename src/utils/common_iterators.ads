------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                     C O M M O N _ I T E R A T O R S                      --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                Copyright (C) 2016-2021, Altran UK Limited                --
--                     Copyright (C) 2016-2021, AdaCore                     --
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

with Types; use Types;

--  This package provides iterators over some of the compiler
--  data-structures that so that its possible to write nicer loops using
--  the "for E of X" syntax. For each kind of iteration there is an "Iter"
--  function that maps a given entity or list to an iterator. For example:
--
--     for E of Iter (Refinement_Constituents (State)) loop
--        ...
--     end loop;
--
--  Sometimes this function takes an additional parameter clarifying which
--  set of functions to use:
--
--     for C of Iter (Components, My_Entity) loop
--        --  uses First_Component and Next_Component
--        ...
--     end loop;

package Common_Iterators is

   -----------
   -- Elist --
   -----------

   type Elist_Wrapper is private
   with Iterable => (First       => ELW_First,
                     Next        => ELW_Next,
                     Has_Element => ELW_Has_Element,
                     Element     => ELW_Element);

   type Elist_Wrapper_Cursor is private;

   function Iter (L : Elist_Id) return Elist_Wrapper;
   --  Iterate over an Elist_Id. If L is No_Elist then we also deal with
   --  this gracefully.

   -----------------------------------------------
   -- Internal functions used for the iterators --
   --                                           --
   -- Do not use these manually!                --
   -----------------------------------------------

   function ELW_First (L : Elist_Wrapper) return Elist_Wrapper_Cursor;

   function ELW_Next (L : Elist_Wrapper;
                      C : Elist_Wrapper_Cursor)
                      return Elist_Wrapper_Cursor;

   function ELW_Has_Element (L : Elist_Wrapper;
                             C : Elist_Wrapper_Cursor)
                             return Boolean;

   function ELW_Element (L : Elist_Wrapper;
                         C : Elist_Wrapper_Cursor)
                         return Node_Or_Entity_Id;

private

   type Elist_Wrapper is new Elist_Id;
   type Elist_Wrapper_Cursor is new Elmt_Id;

   function Iter (L : Elist_Id) return Elist_Wrapper
   is (Elist_Wrapper (L));

end Common_Iterators;
