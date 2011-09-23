------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                      W H Y - G E N - R E C O R D S                       --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                       Copyright (C) 2010-2011, AdaCore                   --
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

with Types;           use Types;

with Why.Ids;         use Why.Ids;
with Why.Gen.Binders; use Why.Gen.Binders;

package Why.Gen.Records is
   --  This package encapsulates the encoding of Ada records into Why.

   --  We are limited to read-only operations on record types for now;
   --  so these are modeled by an abstract type in Why, with one getter
   --  function per field, plus a builder.

   procedure Define_Ada_Record
     (File    : W_File_Id;
      E       : Entity_Id;
      Name    : String;
      Binders : Binder_Array);
   --  Create the declaration of a null record; return its builder logic
   --  function, of the form make___<name> : unit -> <name>.
   --  Output the definition of an Ada record by generating
   --  * its builder
   --    (e.g. make___t (a,b,c) for record type t with three fields);
   --  * its getters
   --    (e.g. get___t_a (obj) for field a of record type t);
   --  its axioms;
   --    one per field, saying that applying a projection on a builder
   --    returns the appropriate result. e.g.
   --
   --  axiom make_get___t_a :
   --   forall (a : t1) (b : t2) (c : t3).
   --    get___t_a (make___t (a,b,c)) = a

end Why.Gen.Records;
