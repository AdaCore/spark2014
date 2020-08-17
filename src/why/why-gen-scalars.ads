------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                      W H Y - G E N - S C A L A R S                       --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                     Copyright (C) 2010-2020, AdaCore                     --
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

with GNATCOLL.Symbols;     use GNATCOLL.Symbols;
with Gnat2Why.Util;        use Gnat2Why.Util;
with SPARK_Atree;          use SPARK_Atree;
with SPARK_Atree.Entities; use SPARK_Atree.Entities;
with Types;                use Types;
with Why.Atree.Modules;    use Why.Atree.Modules;

package Why.Gen.Scalars is
   --  This package implements the generation of Why modules for scalar types
   --  ??? Here is the right place for documentation of the translation of
   --  scalar types, and how this relates to ada__model.mlw

   procedure Create_Fixed_Point_Mult_Div_Theory_If_Needed
     (Typ_Left     : Entity_Id;
      Typ_Right    : Entity_Id;
      Typ_Result   : Entity_Id;
      Expr         : Node_Id)
   with Pre => Nkind (Expr) in N_Op_Multiply | N_Op_Divide | N_Type_Conversion;

   procedure Declare_Scalar_Type
     (Th : Theory_UC;
      E  : Entity_Id)
     with Pre => Is_Scalar_Type (E);
   --  Populate the Theory with all the necessary declarations for Entity E
   --  (which must be a scalar type)

   procedure Define_Scalar_Rep_Proj
     (Th : Theory_UC;
      E  : Entity_Id)
     with Pre => Is_Scalar_Type (E);
   --  Populate the theory associated to the theory of the scalar type E where
   --  the projection to and from the representation type are defined.

   function Get_Fixed_Point_Theory (Typ : Entity_Id) return M_Fixed_Point_Type
   with Pre => Is_Type (Typ);
   --  Return a module name based for operations on fixed-points of type Typ.

   function Get_Fixed_Point_Theory_Name (Typ : Entity_Id) return Symbol
   with Pre => Is_Type (Typ);
   --  Return a unique name based on the values of small of Typ, to be used as
   --  the name of the theory for operations on fixed-points of type Typ.

   function Get_Fixed_Point_Mult_Div_Theory
     (Typ_Left, Typ_Right, Typ_Result : Entity_Id)
      return M_Fixed_Point_Mult_Div_Type
   with Pre => Is_Type (Typ_Left)
     and then Is_Type (Typ_Right)
     and then Is_Type (Typ_Result);
   --  Return a module name based for multiplication/division between
   --  fixed-points of types Typ_Left and Typ_Right resulting in a fixed-point
   --  of type Typ_Result. Typ_Right may be either a fixed-point type, or a
   --  signed integer type for type conversion from Typ_Left to Typ_Result.

   function Get_Fixed_Point_Mult_Div_Theory_Name
     (Typ_Left, Typ_Right, Typ_Result : Entity_Id) return Symbol
   with Pre => Is_Type (Typ_Left)
     and then Is_Type (Typ_Right)
     and then Is_Type (Typ_Result);
   --  Return a unique name based on the values of smalls of the three
   --  fixed-point types involved, to be used as the name of the theory for
   --  multiplication/division between fixed-points of types Typ_Left and
   --  Typ_Right resulting in a fixed-point of type Typ_Result. Typ_Right
   --  may be either a fixed-point type, or a signed integer type for type
   --  conversion from Typ_Left to Typ_Result.

end Why.Gen.Scalars;
