------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                      W H Y - G E N - S C A L A R S                       --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                       Copyright (C) 2010-2014, AdaCore                   --
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

with Types;     use Types;

with Why.Ids;   use Why.Ids;

package Why.Gen.Scalars is
   --  This package provides an interface to generate declarations
   --  (types, subprograms, axioms) for scalar types.

   procedure Declare_Ada_Abstract_Signed_Int
     (Theory  : W_Theory_Declaration_Id;
      Entity  : Entity_Id;
      First   : W_Integer_Constant_Id;
      Last    : W_Integer_Constant_Id;
      Modulus : W_Integer_Constant_Id);
   --  Declare the whole theory for a signed int of the given size,
   --  i.e. whose range is First .. Last. This creates an abstract type
   --  whose name is given in parameter along with a set of axioms and
   --  subprograms for int conversion.  Is_Base is True if the corresponding
   --  Ada type is an Ada base type.

   procedure Declare_Ada_Real
     (Theory  : W_Theory_Declaration_Id;
      Entity  : Entity_Id;
      First   : W_Real_Constant_Id;
      Last    : W_Real_Constant_Id);
   --  Declare the whole theory for a floating/fixed point type whose range
   --  is First .. Last.  This creates an abstract type whose name is
   --  given in parameter along with a set of axioms and subprograms
   --  for real conversion. Is_Base is True if the corresponding Ada type
   --  is an Ada base type.

end Why.Gen.Scalars;
