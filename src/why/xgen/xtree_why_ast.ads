------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                        X T R E E _ W H Y _ A S T                         --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                     Copyright (C) 2010-2021, AdaCore                     --
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

--  This package provides procedures that generate the following code to
--  interface Gnat with Why3:
--
--    1. Ada functions to convert the Xtree Gnat AST to a Json value
--       (procedures Print_Ada_To_Json)
--
--    2. OCaml type definition corresponding to the Xtree Gnat AST as a
--       algebraic datatype
--       (procedures Print_OCaml_*_Type(s))
--
--    3. OCaml functions to convert a Json value to an OCaml Gnat AST
--       (procedures Print_OCaml_*_From_Json)
--
--   The code always deals separately with the enumeration Why_Node, the
--   opaque identifiers, and the enumerations from Why.Sinfo.
--
--   A module in gnatwhy3 converts the AST to the original Why3 AST from
--   Ptree.
--
--      Ada Gnat AST ->(1.) Json ->(3.) OCaml Gnat AST(2.) -> Why3 Ast
--      ^^^^^^ gnat2why ^^^^^ | ^^^^^^^^^^^^^^ gnat2why ^^^^^^^^^^^^^^
--
--  This approach assures that changes in either the Gnat AST or the Why3 Ast

with Outputs; use Outputs;

package Xtree_Why_AST is

   procedure Print_Ada_To_Json (O : in out Output_Record);

   procedure Print_OCaml_Why_Sinfo_Types (O : in out Output_Record);

   procedure Print_OCaml_Why_Node_Type (O : in out Output_Record);

   procedure Print_OCaml_Opaque_Ids (O : in out Output_Record);

   procedure Print_OCaml_Tags (O : in out Output_Record);

   procedure Print_OCaml_Why_Node_From_Json (O : in out Output_Record);

   procedure Print_OCaml_Why_Sinfo_Types_From_Json (O : in out Output_Record);

   procedure Print_OCaml_Opaque_Ids_From_Json (O : in out Output_Record);

   procedure Print_OCaml_Coercions (O : in out Output_Record);

end Xtree_Why_AST;
