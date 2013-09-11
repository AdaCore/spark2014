------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                        G N A T 2 W H Y - U T I L S                       --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                       Copyright (C) 2010-2013, AdaCore                   --
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

--  Utilities for the transformation phase

with Types;            use Types;

with Why.Atree.Tables; use Why.Atree.Tables;
with Why.Ids;          use Why.Ids;
with Why.Inter;        use Why.Inter;

with Gnat2Why.Nodes;   use Gnat2Why.Nodes;

package Gnat2Why.Util is

   Symbol_Table : Ada_Ent_To_Why.Map := Ada_Ent_To_Why.Empty_Map;

   type Transformation_Params is record
      File        : W_File_Id;
      --  Identity of the current Why3 file. If needed, new theories and
      --  modules will be created in this file (e.g. for string literals).
      Theory      : W_Theory_Declaration_Id;
      --  Identity of the current theory or module. New declarations are
      --  emitted in this theory.
      Phase       : Transformation_Phase;
      --  Current transformation phase, which impacts the way code is
      --  transformed from Ada to Why3.
      Gen_Image   : Boolean;
      --  Flag that is True when the transformation should include in the
      --  generated Why3 node a pretty printing label, to be used to show which
      --  part of a possibly large assertion is not proved.
      Ref_Allowed : Boolean;
      --  Flag that is True if references are allowed
   end record;
   --  Set of parameters for the transformation phase

   function Usual_Params (Phase : Transformation_Phase)
                          return Transformation_Params
   is
     (Transformation_Params'(File        => Why_Sections (WF_Main).File,
                             Theory      => Why_Sections (WF_Main).Cur_Theory,
                             Phase       => Phase,
                             Gen_Image   => False,
                             Ref_Allowed => True));
   --  Usual set of transformation parameters for a given phase

   ---------------------------------------------
   -- Usual set of parameters for some phases --
   ---------------------------------------------

   function Body_Params return Transformation_Params is
     (Usual_Params (Generate_VCs_For_Body));

   function Assert_Params return Transformation_Params is
     (Usual_Params (Generate_VCs_For_Assert));

   function Logic_Params return Transformation_Params is
     (Usual_Params (Generate_Logic));

   --------------
   -- Builders --
   --------------

   function Create_Zero_Binding
     (Vars : Node_Lists.List;
      Prog : W_Prog_Id) return W_Prog_Id;
   --  Return a program which binds every variable in Vars to 0 in Prog

   -------------
   -- Queries --
   -------------

   function Expression_Depends_On_Variables (N : Node_Id) return Boolean;
   --  Returns whether the expression E depends on a variable, either directly,
   --  or through the read effects of a function call. This is used to decide
   --  in which output Why file the axiom for the corresponding
   --  constant (for an initialization expression) or the
   --  corresponding aggregate/slice/string literal should be declared.

   function Is_Mutable_In_Why (N : Node_Id) return Boolean;
   --  Given an N_Defining_Identifier, decide if the variable is mutable in
   --  the Why translation

end Gnat2Why.Util;
