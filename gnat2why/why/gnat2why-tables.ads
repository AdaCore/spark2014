------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                       G N A T 2 W H Y - T A B L E S                      --
--                                                                          --
--                                  S p e c                                 --
--                                                                          --
--                     Copyright (C) 2017-2019, AdaCore                     --
--                Copyright (C) 2017-2019, Altran UK Limited                --
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

with Ada.Containers.Hashed_Maps;
with Atree;                       use Atree;
with Common_Containers;           use Common_Containers;
with Einfo;                       use Einfo;
with SPARK_Util;                  use SPARK_Util;
with SPARK_Util.Types;            use SPARK_Util.Types;
with Types;                       use Types;

package Gnat2Why.Tables is

   procedure Store_Information_For_Entity (E : Entity_Id);
   --  @param E any entity that we want to translate in Why3
   --  Store all the necessary information about E in internal tables.

   -------------------------
   -- Component Info Maps --
   -------------------------

   --  For the implementation details: This is one place where we look
   --  at the declaration node to find which discriminant values imply the
   --  presence of which components. We traverse the N_Component_List of the
   --  type declaration, and for each component, and for each N_Variant_Part,
   --  we store a record of type [Component_Info] which contains the N_Variant
   --  node to which the component/variant part belongs, and the N_Variant_Part
   --  to which this N_Variant node belongs. In this way, we can easily access
   --  the discriminant (the Name of the N_Variant_Part) and the discrete
   --  choice (the Discrete_Choices of the N_Variant) of that component or
   --  variant part.

   --  The map [Comp_Info] maps the component entities and N_Variant_Part nodes
   --  to their information record. This map is populated during marking.

   --  We ignore "completely hidden" components of derived record types (see
   --  also the discussion in einfo.ads and sem_ch3.adb)

   type Component_Info is record
      Parent_Variant  : Node_Id;
      Parent_Var_Part : Node_Id;
   end record;

   type Component_Info_Map is private;

   type Component_Visibility is (Regular, Removed, Hidden, Duplicated);

   package Component_Visibility_Maps is new Ada.Containers.Hashed_Maps
     (Key_Type        => Entity_Id,
      Element_Type    => Component_Visibility,
      Hash            => Node_Hash,
      Equivalent_Keys => "=");

   function Component_Is_Visible_In_Type (Rec, Comp : Entity_Id) return Boolean
   with
     Pre => Retysp_Kind (Rec) in Private_Kind | Record_Kind | Concurrent_Kind
     and then Get_Component_Set (Rec).Contains (Comp);
   --  @param Rec is a record type or a protected type
   --  @param Comp component of the record type or of one of its ancestors
   --  @return True if Comp is visible in Rec, that is, it has not been hidden
   --          by a pragma SPARK_Mode (Off), a private derivation, or a
   --          discriminant constraint.

   function Component_Is_Present_In_Type (Rec, Comp : Entity_Id) return Boolean
   with
     Pre  => Retysp_Kind (Rec) in Private_Kind | Record_Kind | Concurrent_Kind
     and then Get_Component_Set (Rec).Contains (Comp),
     Post => Component_Is_Present_In_Type'Result =
       (Get_Component_Visibility_Map (Rec) (Comp) /= Removed);
   --  @param Rec is a record type or a protected type
   --  @param Comp component of the record type or of one of its ancestors
   --  @return True if Comp is present in Rec, that is, it has not been removed
   --          due to a discriminant constraint.

   function Get_Variant_Info (E : Entity_Id) return Component_Info_Map
   with
     Pre => Retysp_Kind (E) in Private_Kind | Record_Kind | Concurrent_Kind;
   --  @param E entity of a type translated as a record in why
   --  @return E's component info from map Comp_Info

   function Get_Component_Info
     (M    : Component_Info_Map;
      Comp : Node_Id)
      return Component_Info;
   --  @param M is a Component_Info_Map for a record type
   --  @param Comp component or a variant part of the record type
   --  @return component info associated to Comp in M.

   function Get_Component_Set (E : Entity_Id) return Node_Sets.Set with
     Pre => Retysp_Kind (E) in Private_Kind | Record_Kind | Concurrent_Kind;
   --  @param E entity of a type translated as a record in why
   --  @return E the set of E's components. It also includes components which
   --  have been defined in E's ancestors but are hidden in E. Components that
   --  are not in SPARK are modeled by the type entity of the first ancestor of
   --  E in which they exist. It also includes Part_Of constituents of
   --  protected objects. Components have the most precise possible type.

   function Get_Component_Visibility_Map
     (E : Entity_Id)
      return Component_Visibility_Maps.Map
   with
     Pre => Retysp_Kind (E) in Private_Kind | Record_Kind | Concurrent_Kind;
   --  @param E entity of a type translated as a record in why
   --  @return E a map from E's components to their visibility. A component has
   --      visibility Regular if it is visible, Hidden if it has been hidden by
   --      a private definition, Duplicate if it is Hidden and some other
   --      regular field has the same name, and Removed if it was removed by
   --      a static constraint.

   function Get_Descendant_Set (E : Entity_Id) return Node_Sets.Set with
     Pre => Is_Tagged_Type (Retysp (E));
   --  @param E entity of a tagged type
   --  @return the set of visible descendants of E.

   function Has_Private_Part (E : Entity_Id) return Boolean with
     Pre => Retysp_Kind (E) in Private_Kind | Record_Kind | Concurrent_Kind;
   --  @param E entity of a type translated as a record in why
   --  @return True if E contains a component for its own private part

   function Has_Variant_Info (Rec, Comp : Entity_Id) return Boolean
   with
     Pre => Retysp_Kind (Rec) in Private_Kind | Record_Kind
     and Ekind (Comp) = E_Component;
   --  @param Rec is a record type or a protected type
   --  @param Comp component of the record type or of one of its ancestors
   --  @return True if Comp is located under a variant.

   function Original_Declaration (Comp : Entity_Id) return Entity_Id
   with
     Pre => Ekind (Comp) in E_Discriminant | E_Component | Type_Kind;
   --  @param Comp component of the record type or of one of its ancestors
   --  @return the first type in the derivation of Scope (Comp) in which Comp
   --          appears.

   function Search_Component_In_Type (Rec, Comp : Entity_Id) return Entity_Id
   with
     Pre => Retysp_Kind (Rec) in Private_Kind | Record_Kind | Concurrent_Kind
     and Ekind (Comp) in E_Discriminant | E_Component | Type_Kind;
   --  @param Rec is a record type or a protected type
   --  @param Comp component of the record type or of one of its ancestors
   --  @return the corresponding component stored in Rec's component
   --          information if any and empty otherwise.
   --          Also supports hidden components.

   function Representative_Component (Comp : Entity_Id) return Entity_Id is
     (Search_Component_In_Type (Original_Declaration (Comp), Comp));

private

   package Component_Info_Maps is new Ada.Containers.Hashed_Maps
     (Key_Type        => Node_Id,
      Element_Type    => Component_Info,
      Hash            => Node_Hash,
      Equivalent_Keys => "=",
      "="             => "=");

   type Component_Info_Map is new Component_Info_Maps.Map with null record;

end Gnat2Why.Tables;
