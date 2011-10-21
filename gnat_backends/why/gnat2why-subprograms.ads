------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                   G N A T 2 W H Y - S U B P R O G R A M S                --
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

with Namet;         use Namet;
with Types;         use Types;
with Why.Ids;       use Why.Ids;
with Why.Types;     use Why.Types;

package Gnat2Why.Subprograms is

   --  This package deals with the translation of GNAT functions and
   --  statements to Why declarations.

   --  Subprograms are translated to Why programs with pre- and postconditions
   --  (contracts). These assertions have to be self-guarded to enforce the
   --  same semantics as if these assertions were executed. For example, an
   --  array access like
   --     X (I) = 0
   --  must be protected by a condition:
   --     I in X'First .. X'Last and then X (I) = 0.
   --  This is checked by generating, for all assertions, equivalent programs
   --  that must be runtime error free.
   --
   --  Subprogram contracts may contain calls to expression functions. As we
   --  have translated these functions to Why logic functions, nothing special
   --  needs to be done.
   --
   --  For a Subprogram *declaration*, we generate a Why parameter
   --  declaration, with the full argument list and the translation of the
   --  contract, if any.
   --
   --  For a Subprogram *body*, we generate a Why program function *without*
   --  parameters (expect a unit parameter); all Ada parameters and local
   --  variables of subprograms, as well as local subprograms, are put at the
   --  global toplevel in Why.
   --
   --  More specific documentation is given at the beginning of each function
   --  in this package.

   procedure Transform_Subprogram
     (File      : W_File_Id;
      Prog_File : W_File_Id;
      Node      : Node_Id;
      As_Spec   : Boolean);
   --  Generate a Why declaration that corresponds to an Ada subprogram
   --  Node is a N_Subprogram_Body

   function Register_Old_Node (N : Node_Id) return Name_Id;
   --  Register a node that appears with attribute 'Old; return a fresh
   --  Name_Id for this Node. This function is intended to be called by the
   --  code that translates expressions to Why (Gnat2why.Expr), which itself
   --  is called by Transform_Subprogram. For each call to this
   --  function, a declaration at the beginning of the Why program is
   --  generated.

   Result_Name : W_Identifier_Id := Why_Empty;

   --  The Name_Id of the currently translated subprogram; intended to be used
   --  by Gnat2why.Expr.Transform_Expr; This variable should be equal to
   --  Why_Empty whenever we do *not* translate program expressions.

end Gnat2Why.Subprograms;
