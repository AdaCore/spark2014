------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                             A L F A . U T I L                            --
--                                                                          --
--                                  S p e c                                 --
--                                                                          --
--                        Copyright (C) 2012, AdaCore                       --
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
-- gnat2why is maintained by AdaCore (http://www.adacore.com)               --
--                                                                          --
------------------------------------------------------------------------------

package Alfa.Util is

   function Aggregate_Is_Fully_Initialized (N : Node_Id) return Boolean;
   --  Return whether aggregate N is fully initialized

   function All_Aggregates_Are_Fully_Initialized
     (N : Node_Id) return Boolean;
   --  Return whether all aggregates in node N (recursively) are fully
   --  initialized.

   function Expression_Functions_All_The_Way (E : Entity_Id) return Boolean;
   --  Given the entity E for a function, determine whether E is an expression
   --  function that only calls expression functions, directly or indirectly.

   procedure Add_Full_And_Partial_View (Full, Partial : Entity_Id);
   --  Store the correspondance between the Full and Partial views of the same
   --  entity, for deferred constants and private types.

   function Is_Full_View (E : Entity_Id) return Boolean;
   --  Return whether E is the full view of another entity

   function Partial_View (E : Entity_Id) return Entity_Id;
   --  Return the partial view for entity E

   function Most_Underlying_Type (E : Entity_Id) return Entity_Id;
   --  Takes a type E in parameter. If E is a private type or a record subtype,
   --  follow the chain of underlying types (for a private type) and base types
   --  (for a record subtype) to return the first non-private type which is not
   --  also a record subtype. Otherwise, return E.

end Alfa.Util;
