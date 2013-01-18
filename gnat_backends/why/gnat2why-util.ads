------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                      G N A T 2 W H Y - D R I V E R                       --
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

with Why.Atree.Tables; use Why.Atree.Tables;
with Why.Ids;          use Why.Ids;
with Why.Inter;        use Why.Inter;

with Gnat2Why.Nodes;   use Gnat2Why.Nodes;

package Gnat2Why.Util is

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
      Name_Map    : Ada_Ent_To_Why.Map;
      --  Map from Ada entities to Why entities used for subprogram parameters
      --  in specs, which should be translated differently from global
      --  variables.
   end record;
   --  Set of parameters for the transformation phase

   function Usual_Params (Phase : Transformation_Phase)
                          return Transformation_Params
   is
     (Transformation_Params'(File        => Why_Files (WF_Main).File,
                             Theory      => Why_Files (WF_Main).Cur_Theory,
                             Phase       => Phase,
                             Gen_Image   => False,
                             Ref_Allowed => True,
                             Name_Map    => Ada_Ent_To_Why.Empty_Map));
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

end Gnat2Why.Util;
