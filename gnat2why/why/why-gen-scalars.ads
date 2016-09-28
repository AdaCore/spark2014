------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                      W H Y - G E N - S C A L A R S                       --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                       Copyright (C) 2010-2016, AdaCore                   --
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

with Einfo;         use Einfo;
with Gnat2Why.Util; use Gnat2Why.Util;
with Types;         use Types;

package Why.Gen.Scalars is
   --  This package implements the generation of Why modules for scalar types
   --  ??? Here is the right place for documentation of the translation of
   --  scalar types, and how this relates to ada__model.mlw

   procedure Declare_Scalar_Type
     (File : W_Section_Id;
      E    : Entity_Id)
     with Pre => Is_Scalar_Type (E);
   --  Populate the Theory with all the necessary declarations for Entity E
   --  (which must be a scalar type)

   procedure Define_Scalar_Rep_Proj
     (File : W_Section_Id;
      E    : Entity_Id)
     with Pre => Is_Scalar_Type (E);
   --  Populate the theory associated to the theory of the scalar type E where
   --  the projection to and from the representation type are defined.

end Why.Gen.Scalars;
