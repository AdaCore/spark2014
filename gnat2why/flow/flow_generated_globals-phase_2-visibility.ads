------------------------------------------------------------------------------
--                                                                          --
--                           GNAT2WHY COMPONENTS                            --
--                                                                          --
--       F L O W . G E N E R A T E D _ G L O B A L S . P H A S E _ 2        --
--                            V I S I B I L I T Y                           --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                  Copyright (C) 2018, Altran UK Limited                   --
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

private package Flow_Generated_Globals.Phase_2.Visibility is

   type Name_Scope is record
      Ent  : Any_Entity_Name;
      Part : Any_Declarative_Part;
   end record;
   --  Just like Flow_Scope, but for Entity_Names

   type Name_Info_T is record
      Is_Package      : Boolean;
      Is_Private      : Boolean;

      Parent          : Any_Entity_Name;
      Instance_Parent : Any_Entity_Name;
      Template        : Any_Entity_Name;
      Container       : Name_Scope;
   end record;
   --  A minimal description of a name location within the code hierarchy

   procedure Register_Name_Scope (E : Entity_Name; Info : Name_Info_T);
   --  Add vertices for E to name visibility graph

   procedure Connect_Name_Scopes;
   --  Creates edges in the visibility graph

   function State_Refinement_Is_Visible
     (State  : Entity_Name;
      Caller : Entity_Name)
      return Boolean
   with Pre => GG_Is_Abstract_State (State);

   function Part_Of_Is_Visible
     (State  : Entity_Name;
      Caller : Entity_Name)
      return Boolean
   with Pre => GG_Is_Abstract_State (State);

   procedure Up_Project (Vars      :     Name_Sets.Set;
                         Caller    :     Entity_Name;
                         Projected : out Name_Sets.Set;
                         Partial   : out Name_Sets.Set);
   --  ??? This routine historically belongs to Flow_Refinement, but we can't
   --  have it there and keep this a private child of Phase_2.
   --  Note that here we only have the Caller parameter and not a full scope.

   procedure Up_Project (Vars           :     Global_Names;
                         Projected_Vars : out Global_Names;
                         Caller         :     Entity_Name);

--     procedure Dump_Tree;
--     --  Print the inter

end Flow_Generated_Globals.Phase_2.Visibility;
