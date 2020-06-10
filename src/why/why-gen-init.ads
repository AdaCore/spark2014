------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                          W H Y - G E N - I N I T                         --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                     Copyright (C) 2018-2020, AdaCore                     --
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

with Gnat2Why.Util;            use Gnat2Why.Util;
with SPARK_Atree.Entities;     use SPARK_Atree.Entities;
with SPARK_Util.Types;         use SPARK_Util.Types;
with Types;                    use Types;
with Why.Atree.Accessors;      use Why.Atree.Accessors;
with Why.Conversions;          use Why.Conversions;
with Why.Ids;                  use Why.Ids;
with Why.Sinfo;                use Why.Sinfo;

package Why.Gen.Init is
   --  This package encapsulates the encoding of initialization by proof.

   procedure Declare_Init_Wrapper (P : W_Section_Id; E : Entity_Id) with
     Pre => Is_Type (E);
   --  Add declarations for a wrapper type for E in P

   function Is_Init_Wrapper_Type (Typ : W_Type_Id) return Boolean;

   function EW_Init_Wrapper (Ty : W_Type_Id) return W_Type_Id with
     Pre => Get_Type_Kind (Ty) in EW_Abstract | EW_Split
     and then Might_Contain_Relaxed_Init (Get_Ada_Node (+Ty));
   --  Return the init wrapper type with the same ada node and kind as Ty

   function Compute_Is_Initialized
     (E                      : Entity_Id;
      Name                   : W_Expr_Id;
      Ref_Allowed            : Boolean;
      Domain                 : EW_Domain;
      Exclude_Always_Relaxed : Boolean := False)
      return W_Expr_Id;
   --  Whether Name is initialized. This does not only include the top level
   --  initialization flag of E but also the flags of nested components for
   --  composite types.
   --  If Exclude_Always_Relaxed is True, do not include initialization of
   --  subcomponents whose type is annotated with relaxed initialization. A
   --  part of an expression which has relaxed initialization may not be of a
   --  type with relaxed initialization, for example, if it comes from an
   --  object which has relaxed initialization, or if it is a part of a
   --  composite expression which itself has a type with relaxed
   --  initialization. Some initialization checks are only interested with
   --  these parts which do not have a type with relaxed initialization. This
   --  happens for example when storing the expression in an object of its
   --  type, or when giving it as a parameter to a function call.

   function Insert_Initialization_Check
     (Ada_Node               : Node_Id;
      E                      : Entity_Id;
      Name                   : W_Expr_Id;
      Domain                 : EW_Domain;
      Exclude_Always_Relaxed : Boolean := False)
      return W_Expr_Id;
   --  If Domain = EW_Prog, insert a check that Name is initialized

   function To_Init_Module (Name : W_Identifier_Id) return W_Identifier_Id;
   --  For an identifier from the module of an entity (queried from E_Symb
   --  for example) return the same symbol but in the init wrapper module.

end Why.Gen.Init;
