------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                      S P A R K _ D E F I N I T I O N                     --
--                                                                          --
--                                  S p e c                                 --
--                                                                          --
--                     Copyright (C) 2011-2019, AdaCore                     --
--                Copyright (C) 2014-2019, Altran UK Limited                --
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

---------------------------------
-- Detection of SPARK Entities --
---------------------------------

--  All entities from the program are marked as being in SPARK or not in SPARK.
--  Their marking status determines how they are translated to Why3 and the
--  marking order determines the order of definition in Why3.

--  An error is issued if an entity which should be in SPARK, according to the
--  applicable SPARK_Mode pragma, is not in SPARK.

--  All entities declared locally to a toplevel subprogram body are either all
--  in SPARK, and listed for translation, or not listed for translation if a
--  violation was detected in the body.

with Atree;                             use Atree;
with Common_Containers;                 use Common_Containers;
with Einfo;                             use Einfo;
with GNATCOLL.JSON;                     use GNATCOLL.JSON;
with Sinfo;                             use Sinfo;
with SPARK_Util;                        use SPARK_Util;
with SPARK_Util.Subprograms;            use SPARK_Util.Subprograms;
with Types;                             use Types;

package SPARK_Definition is

   ----------------------------------------------------------------------
   --  Settings
   ----------------------------------------------------------------------

   Max_Array_Dimensions : constant Positive := 4;
   --  Maximal number of array dimensions that are currently supported

   procedure Inhibit_Messages;
   --  Disable error messages during marking when generating globals (only
   --  the marking itself is important). Use this procedure only once, before
   --  starting the marking itself.

   ----------------------------------------------------------------------
   --  Marking procedures
   ----------------------------------------------------------------------

   function Is_Clean_Context return Boolean with Ghost;
   --  Returns True iff the global variables that should be manipulated by
   --  marking in a stack fashion have been properly restored.

   procedure Mark_Compilation_Unit (N : Node_Id)
     with Pre => Nkind (N) in N_Generic_Package_Declaration
                            | N_Generic_Subprogram_Declaration
                            | N_Generic_Package_Renaming_Declaration
                            | N_Generic_Function_Renaming_Declaration
                            | N_Generic_Procedure_Renaming_Declaration
                            | N_Package_Body
                            | N_Package_Declaration
                            | N_Package_Renaming_Declaration
                            | N_Subprogram_Body
                            | N_Subprogram_Declaration
                            | N_Subprogram_Renaming_Declaration
                  and then Is_Clean_Context,
          Post => Is_Clean_Context;
   --  Put marks on a compilation unit. This should be called after all
   --  compilation units on which this compilation unit depends have been
   --  marked.

   ----------------------------------------------------------------------
   --  Marking results queries
   ----------------------------------------------------------------------

   function Entity_Marked (E : Entity_Id) return Boolean;
   --  Returns True if entity E has already been considered for marking
   --  ??? Exposing this function seems suspiocious; it is only used by Retysp

   function Entity_In_SPARK (E : Entity_Id) return Boolean with
     Pre => Ekind (E) not in E_Abstract_State  |
                             E_Package_Body    |
                             E_Protected_Body  |
                             E_Subprogram_Body |
                             E_Task_Body       |
                             Generic_Unit_Kind;
   --  Returns True if entity E is in SPARK. Note that E may be in SPARK
   --  without being marked by the user in SPARK, in which case it can be
   --  called from SPARK code, but no VC will be generated for E.
   --
   --  Also note that for specification entities it only checks that the
   --  specification itself is in SPARK, i.e. the entity may be referenced
   --  from SPARK code.
   --
   --  This call is only allowed for entities that are referenced from other
   --  code, i.e. almost anything except E_Package (since packages are never
   --  referenced), body entities (since their status should be queried with a
   --  dedicated function), and generic units (which should be expanded by the
   --  front end).

   function Entity_Spec_In_SPARK (E : Entity_Id) return Boolean with
     Pre => Ekind (E) in Entry_Kind       |
                         E_Function       |
                         E_Package        |
                         E_Procedure      |
                         E_Protected_Type |
                         E_Task_Type;
   --  @param E an entity
   --  @return True if the spec of E was marked in SPARK. Note this does not
   --    mean that the entity is valid SPARK, only that SPARK_Mode is On.

   function Entity_Body_In_SPARK (E : Entity_Id) return Boolean with
     Pre => Ekind (E) in Entry_Kind       |
                         E_Function       |
                         E_Package        |
                         E_Procedure      |
                         E_Protected_Type |
                         E_Task_Type;
   --  Returns True iff the body of E was marked in SPARK and contains no SPARK
   --  violations.

   function Entity_Body_Compatible_With_SPARK (E : Entity_Id) return Boolean
   with
     Pre => Ekind (E) in E_Function
              and then Present (Get_Expression_Function (E));
   --  Returns True iff the body of expression function E contains no SPARK
   --  violations.

   function Private_Spec_In_SPARK (E : Entity_Id) return Boolean with
     Pre => Ekind (E) in E_Package        |
                         E_Protected_Type |
                         E_Task_Type;
   --  Returns True iff the private part of spec is in SPARK

   function Body_Statements_In_SPARK (E : Entity_Id) return Boolean with
     Pre => Ekind (E) = E_Package and then Entity_Body_In_SPARK (E);
   --  Returns True iff the package body statements are in SPARK. Only
   --  applicable to packages, whose body itself is in SPARK.

   function Full_View_Not_In_SPARK (E : Entity_Id) return Boolean
     with Pre => Is_Type (E);
   --  Returns True if the underlying type of the type E is not in SPARK,
   --  declared in a private part with SPARK_Mode => Off or in a private part
   --  of a package with external axioms. Also returns True if E is a subtype
   --  or derived type of such an entity.

   function Get_SPARK_JSON return JSON_Array;
   --  Should be called after marking is finished. Returns the result of
   --  marking as a JSON record.

   function Is_Actions_Entity (E : Entity_Id) return Boolean;
   --  Returns True iff entity E is defined in actions and thus requires a
   --  special translation. See gnat2why.ads for details.

   function Is_Loop_Entity (E : Entity_Id) return Boolean;
   --  Returns True iff entity E is defined in loop before the invariants and
   --  thus may require a special translation. See gnat2why.ads for details.

   procedure Mark_Iterable_Aspect (Iterable_Aspect : Node_Id);
   --  Mark functions mentioned in the Iterable aspect of a type.
   --  ??? This function is currently public because it is used by
   --  SPARK_Annotate, which is conceptually part of marking. We should
   --  integrate SPARK_Annotate into Marking (via a child package?) to
   --  avoid this internal call in the public API.

   procedure Mark_Standard_Package;
   --  Put marks on package Standard

   function Has_Incomplete_Access (E : Entity_Id) return Boolean with
     Pre => Is_Type (E);
   --  Return True if E is the full view of an incomplete type

   function Get_Incomplete_Access (E : Entity_Id) return Entity_Id with
     Pre  => Is_Type (E) and then Has_Incomplete_Access (E),
     Post => Present (Get_Incomplete_Access'Result)
     and then Is_Access_Type (Get_Incomplete_Access'Result);
   --  Return an access type to E

   ----------------------------------------------------------------------
   --  Marked entity collections
   ----------------------------------------------------------------------

   type Entity_Collection is (Entities_To_Translate)
   with Iterable => (First       => First_Cursor,
                     Next        => Next_Cursor,
                     Has_Element => Has_Element,
                     Element     => Get_Element);

   type Cursor is private;

   function First_Cursor (Kind : Entity_Collection)
                          return Cursor;

   function Next_Cursor (Kind : Entity_Collection;
                         C    : Cursor)
                         return Cursor;

   function Has_Element (Kind : Entity_Collection;
                         C    : Cursor)
                         return Boolean;

   function Get_Element (Kind : Entity_Collection;
                         C    : Cursor)
                         return Entity_Id;

private

   type Cursor is new Node_Lists.Cursor;

end SPARK_Definition;
