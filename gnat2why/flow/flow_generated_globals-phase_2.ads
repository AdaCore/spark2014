------------------------------------------------------------------------------
--                                                                          --
--                           GNAT2WHY COMPONENTS                            --
--                                                                          --
--       F L O W . G E N E R A T E D _ G L O B A L S . P H A S E _ 2        --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--               Copyright (C) 2014-2016, Altran UK Limited                 --
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

with Atree;                              use Atree;
with Einfo;                              use Einfo;
with Flow_Dependency_Maps;               use Flow_Dependency_Maps;
with Flow_Refinement;                    use Flow_Refinement;
with Sinfo;                              use Sinfo;

package Flow_Generated_Globals.Phase_2 is

   -------------------------
   -- Reading & Computing --
   -------------------------

   procedure GG_Read (GNAT_Root : Node_Id)
   with Pre  => Nkind (GNAT_Root) = N_Compilation_Unit
                and then GG_Mode = GG_No_Mode,
        Post => GG_Mode = GG_Read_Mode;
   --  Reads all ALI files and produce the transitive closure.

   --------------
   -- Querying --
   --------------

   function GG_Has_Been_Generated return Boolean;
   --  Checks if the Globals Graph has been generated.
   --  @return True iff the Globals Graph has been generated

   function GG_Exist (E : Entity_Id) return Boolean
   with Pre => GG_Mode = GG_Read_Mode;
   --  Returns True if generated globals have been computed for the
   --  given entity.

   function GG_Has_Refinement (EN : Entity_Name) return Boolean
   with Pre => GG_Mode = GG_Read_Mode;
   --  Returns true if E is a state abstraction whose constituents we
   --  loaded while reading the ALI files.

   function GG_Is_Constituent (EN : Entity_Name) return Boolean
   with Pre => GG_Mode = GG_Read_Mode;
   --  Returns true if E is a constituent of some state abstraction
   --  that we loaded while reading the ALI files.

   function GG_Get_Constituents (EN : Entity_Name) return Name_Sets.Set
   with Pre => GG_Mode = GG_Read_Mode;
   --  Returns the set of direct constituents of a state abstraction
   --  or an Empty_Set if they do not exist.

   function GG_Enclosing_State (EN : Entity_Name) return Entity_Name
   with Pre => GG_Mode = GG_Read_Mode;
   --  Returns the Entity_Name of the directly enclosing state. If one
   --  does not exist it returns Null_Entity_Name.

   function GG_Fully_Refine (EN : Entity_Name) return Name_Sets.Set
   with Pre => GG_Mode = GG_Read_Mode and then
               GG_Has_Refinement (EN);
   --  Returns the most refined constituents of state abstraction EN.

   procedure GG_Get_Globals (E           : Entity_Id;
                             S           : Flow_Scope;
                             Proof_Reads : out Flow_Id_Sets.Set;
                             Reads       : out Flow_Id_Sets.Set;
                             Writes      : out Flow_Id_Sets.Set)
   with Pre  => GG_Mode = GG_Read_Mode and then
                GG_Exist (E),
        Post => GG_Mode = GG_Read_Mode;
   --  Determines the set of all globals.

   function GG_Get_All_State_Abstractions return Name_Sets.Set
   with Pre => GG_Mode = GG_Read_Mode;
   --  @return a set of Entity_Names with all the state abstractions
   --    that the Generated Globals know of.

   function GG_Get_Initializes
     (EN : Entity_Name;
      S  : Flow_Scope)
      return Dependency_Maps.Map
   with Pre => GG_Has_Been_Generated;
   --  @param EN is the entity name whose generated initialize aspect we want
   --  @param S is the Flow_Scope at which we need to up project the results
   --  @return the generated initializes if it exists or an empty dependency
   --    map otherwise.

   function GG_Get_Local_Variables
     (EN : Entity_Name)
      return Name_Sets.Set
   with Pre => GG_Has_Been_Generated;
   --  This function takes as a parameter the name of a package and returns a
   --  set of names comprising:
   --    * all variables declared directly inside the package,
   --    * variables declared in the private part of nested packages that are
   --      in SPARK and do NOT have a user-provided Initializes aspect and
   --    * variables introduced in the declarations of the body part of nested
   --      packages that are in SPARK and do NOT have a user-provided
   --      Abstract_State aspect.
   --  Constants with variable inputs are also included in the above.
   --
   --  @param EN is the entity name whose local variables we are asking for
   --  @return the set of Entity_Names of the local variables as recorded
   --    by the generated globals

   function GG_Is_Initialized_At_Elaboration (EN : Entity_Name) return Boolean
   with Pre => GG_Has_Been_Generated;
   --  @param EN is the entity name we want to check
   --  @return True iff EN is initialized at elaboration

   function GG_Is_Volatile (EN : Entity_Name) return Boolean
   with Pre => GG_Has_Been_Generated;
   --  @param EN is the entity name that we check for being volatile
   --  @return True iff EN is volatile.

   function GG_Has_Async_Writers (EN : Entity_Name) return Boolean
   with Pre  => GG_Has_Been_Generated,
        Post => (if GG_Has_Async_Writers'Result
                 then GG_Is_Volatile (EN));
   --  @param EN is the entity name that we check for having Async_Writers
   --  @return True iff EN has Async_Writers set.

   function GG_Has_Async_Readers (EN : Entity_Name) return Boolean
   with Pre  => GG_Has_Been_Generated,
        Post => (if GG_Has_Async_Readers'Result
                 then GG_Is_Volatile (EN));
   --  @param EN is the entity name that we check for having Async_Readers
   --  @return True iff EN has Async_Readers set.

   function GG_Has_Effective_Reads (EN : Entity_Name) return Boolean
   with Pre  => GG_Has_Been_Generated,
        Post => (if GG_Has_Effective_Reads'Result
                 then GG_Has_Async_Writers (EN));
   --  @param EN is the entity name that we check for having Effective_Reads
   --  @return True iff EN has Effective_Reads set.

   function GG_Has_Effective_Writes (EN : Entity_Name) return Boolean
   with Pre  => GG_Has_Been_Generated,
        Post => (if GG_Has_Effective_Writes'Result
                 then GG_Has_Async_Readers (EN));
   --  @param EN is the entity name that we check for having Effective_Writes
   --  @return True iff EN has Effective_Writes set.

   function Is_Potentially_Blocking (E : Entity_Id) return Boolean
   with Pre => GG_Has_Been_Generated and then
               Ekind (E) in E_Entry | E_Procedure | E_Function;
   --  Returns True if subprogram E is potentially blocking or its blocking
   --  status is unknown; returns False it if is known to be nonblocking.

   function Tasking_Objects
     (Kind : Tasking_Info_Kind;
      Subp : Entity_Name)
      return Name_Sets.Set
   with Pre => GG_Has_Been_Generated;
   --  Returns the set of objects (e.g. suspension objects or entries,
   --  depending on the Kind) accessed by a main-like subprogram Subp.

   function Directly_Called_Protected_Objects
     (Ent : Entity_Name) return Name_Sets.Set
   with Pre => Ent /= Null_Entity_Name;
   --  @param Ent an entity name that refers to a task, main-like subprogram or
   --    protected operation
   --  @return the set of protected operations that are called "directly", that
   --    is without going through other protected operations

   package Object_Priority_Lists is
     new Ada.Containers.Doubly_Linked_Lists (Element_Type => Priority_Value);
   --  Containers with priorities of protected components

   function Component_Priorities
     (Obj : Entity_Name)
      return Object_Priority_Lists.List
   with
     Post => not Object_Priority_Lists.Is_Empty (Component_Priorities'Result);
   --  @param Obj an entity name that refers to a library-level object with
   --    protected components
   --  @return priorities of protected object components

end Flow_Generated_Globals.Phase_2;
