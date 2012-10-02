------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                      G N A T 2 W H Y - D R I V E R                       --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                       Copyright (C) 2010-2012, AdaCore                   --
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
--  This package is the main driver for the Gnat2Why translation. It is
--  invoked by the gnat1 driver.
--
--  The main job of this package is to traverse the list of declarations of a
--  Gnat package, detect the kind of each declaration and dispatch to the
--  packages that deal with type declarations, data declarations and
--  function/procedure definitions.

with Types;          use Types;
with Why.Ids;        use Why.Ids;
with Why.Inter;      use Why.Inter;

with Gnat2Why.Nodes; use Gnat2Why.Nodes;

package Gnat2Why.Driver is

   type Translation_Phase is (Translation,
                              Generate_VCs_For_Pre,
                              Generate_VCs_For_Post,
                              Generate_VCs_For_Assert,
                              Generate_VCs_For_Body,
                              Generate_Contract_For_Body);

   subtype Generate_VCs is Translation_Phase range
     Generate_VCs_For_Pre ..
     --  Generate_VCs_For_Post
     --  Generate_VCs_For_Assert
     Generate_VCs_For_Body;

   subtype Generate_VCs_For_Assertion is Translation_Phase range
     Generate_VCs_For_Pre ..
     --  Generate_VCs_For_Post
     Generate_VCs_For_Assert;

   subtype Generate_For_Body is Translation_Phase range
     Generate_VCs_For_Body ..
       Generate_Contract_For_Body;

   type Translation_Params is record
      File        : W_File_Id;
      Theory      : W_Theory_Declaration_Id;
      Phase       : Translation_Phase;
      Gen_Image   : Boolean;
      Ref_Allowed : Boolean;
      Name_Map    : Ada_Ent_To_Why.Map;
   end record;
   --  File        - the current File_id which is populated by theories;
   --                this is used to insert new theories on the fly, e.g. for
   --                string literals
   --  Theory      - the current theory, used to emit declarations
   --  Phase       - the phase, changes some translations
   --  Ref_Allowed - if references are allowed in the term to be generated
   --  Name_Map    - A map from Ada entities to Why entities; this is used
   --                for subprogram parameters in specs, which should be
   --                translated differently from global variables

   function Body_Params return Translation_Params is
     (Translation_Params'(File        => Why_Files (WF_Main).File,
                          Theory      => Why_Files (WF_Main).Cur_Theory,
                          Phase       => Generate_VCs_For_Body,
                          Gen_Image   => False,
                          Ref_Allowed => True,
                          Name_Map    => Ada_Ent_To_Why.Empty_Map));

   function Assert_Params return Translation_Params is
     (Translation_Params'(File        => Why_Files (WF_Main).File,
                          Theory      => Why_Files (WF_Main).Cur_Theory,
                          Phase       => Generate_VCs_For_Assert,
                          Gen_Image   => False,
                          Ref_Allowed => True,
                          Name_Map    => Ada_Ent_To_Why.Empty_Map));
   --  Set of parameters for the transformation of an Ada assertion into a Why3
   --  program that checks the absence of run-time errors and checks that the
   --  assertion holds.

   function Term_Params return Translation_Params is
     (Translation_Params'(File        => Why_Files (WF_Main).File,
                          Theory      => Why_Files (WF_Main).Cur_Theory,
                          Phase       => Translation,
                          Gen_Image   => False,
                          Ref_Allowed => True,
                          Name_Map    => Ada_Ent_To_Why.Empty_Map));

   procedure GNAT_To_Why (GNAT_Root : Node_Id);
   --  Translates an entire GNAT tree for a compilation unit into
   --  a set of Why sources. This is the main driver for the
   --  Ada-to-Why back end and is invoked by Gnat1drv.

   function Is_Back_End_Switch (Switch : String) return Boolean;
   --  Returns True if and only if Switch denotes a back-end switch

   procedure Translate_Standard_Package;
   --  Translate the Ada Standard package

end Gnat2Why.Driver;
