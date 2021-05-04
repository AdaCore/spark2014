------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--        F L O W . G E N E R A T E D _ G L O B A L S . P A R T I A L       --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                Copyright (C) 2016-2021, Altran UK Limited                --
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
------------------------------------------------------------------------------

--  ### This generates globals (in phase 1). Package Phase_1 deals
--  with reading and writing to ALI files, but this is where the magic
--  happens.
--  ### Possibly rename after merge

with SPARK_Util; use SPARK_Util;

package Flow_Generated_Globals.Partial is

   procedure Generate_Contracts (GNAT_Root : Node_Id);
   --  ??? perhaps this could be a library-level procedure and not a package

   --  The remaining declarations constitute the interface between the phase-1
   --  globals generation and saving the results in the ALI file.
   --
   --  ??? most likely this should be moved once the new serialization is done

   function Is_Callee (E : Entity_Id) return Boolean;
   --  Returns True iff E might be called or is a nested package (whose
   --  elaboration is handled as a call).

   subtype Callee_Set is Node_Sets.Set
   with Dynamic_Predicate =>
          (for all E of Callee_Set => Is_Callee (E));

   type Call_Nodes is record
      Proof_Calls       : Callee_Set;
      Conditional_Calls : Callee_Set;
      Definite_Calls    : Callee_Set;
   end record
   with Dynamic_Predicate => Disjoint (Call_Nodes.Proof_Calls,
                                       Call_Nodes.Conditional_Calls,
                                       Call_Nodes.Definite_Calls);

   function Disjoint (A, B, C : Node_Sets.Set) return Boolean;
   --  Returns True iff sets A, B, C are mutually disjoint

   subtype Pkg_State_Set is Global_Set
   with Dynamic_Predicate =>
          (for all E of Pkg_State_Set => Is_Package_State (E));

   type Initializes_Nodes is record
      Proper  : Pkg_State_Set;  --  ??? Abstract, just like in Flow_Nodes
      Refined : Pkg_State_Set;
   end record;

   type Flow_Nodes is record
      Proper  : Global_Nodes;  --  ??? Abstract
      Refined : Global_Nodes;

      Initializes : Initializes_Nodes;
      --  Only meaningful for packages

      Calls : Call_Nodes;
      --  ### This is all the calls relevant for generation of
      --  globals, i.e. calls to subprograms *with* contracts do not
      --  appear here because we already understand the effects.
   end record;
   --  Information needed to synthesize the Global contract

end Flow_Generated_Globals.Partial;
