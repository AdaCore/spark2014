------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                            C E _ P A R S I N G                           --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                     Copyright (C) 2022-2023, AdaCore                     --
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

with CE_Values;                use CE_Values;
with SPARK_Atree.Entities;     use SPARK_Atree.Entities;
with Types;                    use Types;
with VC_Kinds;                 use VC_Kinds;

package CE_Parsing is

   function Get_Counterexample_Value
     (Obj      : Entity_Id;
      Cnt_List : Cntexample_Elt_Lists.List) return Opt_Value_Type;
   --  Go over a list of raw Why3 counterexample values and construct the value
   --  of Obj if any.

   procedure Parse_Counterexample_Line
     (Cnt_List  : Cntexample_Elt_Lists.List;
      Value_Map : in out Entity_To_Extended_Value_Maps.Map);
   --  Go over a list of raw Why3 counterexample values and transform them into
   --  a map of counterexample values.

   Parse_Error : exception;

   function Parse_Scalar_Value
     (Cnt_Value : Cntexmp_Value;
      AST_Type  : Entity_Id) return Scalar_Value_Type
   with Pre => Is_Scalar_Type (AST_Type);
   --  Parse a counterexample value as a value of AST_Type. If it cannot be
   --  parsed that way, Parse_Error is raised.

end CE_Parsing;
