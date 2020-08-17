------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                       G N A T 2 W H Y - T A B L E S                      --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                     Copyright (C) 2017-2020, AdaCore                     --
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

with Common_Iterators;                   use Common_Iterators;
with Namet;                              use Namet;
with Nlists;                             use Nlists;
with Sem_Aux;                            use Sem_Aux;
with Sem_Util;                           use Sem_Util;
with Sinfo;                              use Sinfo;
with SPARK_Definition;                   use SPARK_Definition;

package body Gnat2Why.Tables is

   type Record_Info is record
      Components   : Node_Sets.Set;
      Variant_Info : Component_Info_Map;
      Visibility   : Component_Visibility_Maps.Map;
   end record
     with Dynamic_Predicate =>
       (for all E of Components => Visibility.Contains (E));

   package Component_Info_Map_Maps is new Ada.Containers.Hashed_Maps
     (Key_Type        => Entity_Id,
      Element_Type    => Record_Info,
      Hash            => Node_Hash,
      Equivalent_Keys => "=");

   package Descendant_Maps is new Ada.Containers.Hashed_Maps
     (Key_Type        => Entity_Id,
      Element_Type    => Node_Sets.Set,
      Hash            => Node_Hash,
      Equivalent_Keys => "=",
      "="             => Node_Sets."=");

   Comp_Info   : Component_Info_Map_Maps.Map :=
     Component_Info_Map_Maps.Empty_Map;
   --  This map maps record types and protected types to a map mapping each
   --  component and each N_Variant node to a Component_Info record. This map
   --  is populated through calls to Init_Component_Info and
   --  Init_Component_Info_For_Protected_Types.

   Descendants : Descendant_Maps.Map;
   --  This map maps tagged types to all their descendants that are visible
   --  from the analyzed unit.

   function Find_Rec_Node_For_Variant (E : Entity_Id) return Entity_Id
   with Pre => Retysp_Kind (E) in Private_Kind | Record_Kind | Concurrent_Kind;
   --  @param E record type
   --  @return the entity to be used to query the variant information for E

   procedure Init_Component_Info (E : Entity_Id)
   with Pre => Ekind (E) in Record_Kind | Private_Kind;
   --  @param E record type
   --  For each subcomponent of E, create an entry in map Comp_Info

   procedure Init_Component_Info
     (E          : Entity_Id;
      Info       : in out Record_Info;
      Visibility : Component_Visibility);
   --  Same as Init_Component_Info (E : Entity_Id) except that information
   --  about E's fields is stored in Info.
   --  @param E record type
   --  @param Info information that should be updated
   --  @param Visibility which should be used for components of E

   procedure Init_Component_Info_For_Protected_Types (E : Entity_Id)
   with Pre => Is_Concurrent_Type (E);
   --  @param E the entity of the concurrent type
   --  For each component and discriminant of E, create an entry in map
   --  Comp_Info.

   procedure Init_Component_Info_For_Subtypes
     (E    : Entity_Id;
      Info : in out Record_Info);
   --  @param E record or concurrent subtype
   --  For each subcomponent of E, create an entry in map Comp_Info

   function Search_Component_In_Info
     (Info         : Node_Sets.Set;
      Comp         : Entity_Id;
      Is_Duplicate : out Boolean)
      return Entity_Id
   with Pre => Ekind (Comp) in E_Component | Type_Kind;
   --  @param Info component set
   --  @param Comp record component, or discriminant, or part_of object
   --  @param Is_Duplicate True if there is a component in Comp which has the
   --    same name as Comp.
   --  @result An entity with same name and same original component as Comp in
   --      Info if any.

   procedure Store_In_Ancestors (E : Entity_Id) with
     Pre => Is_Tagged_Type (Root_Retysp (E));
   --  @param E a tagged record type
   --  Store E in the descendant map of each of its ancestors

   ----------------------------------
   -- Component_Is_Present_In_Type --
   ----------------------------------

   function Component_Is_Present_In_Type (Rec, Comp : Entity_Id) return Boolean
   is
      Ty : constant Entity_Id :=
        Retysp (if Is_Class_Wide_Type (Rec)
                then Get_Specific_Type_From_Classwide (Rec) else Rec);
   begin
      return Comp_Info (Ty).Visibility (Comp) /= Removed;
   end Component_Is_Present_In_Type;

   ----------------------------------
   -- Component_Is_Visible_In_Type --
   ----------------------------------

   function Component_Is_Visible_In_Type (Rec, Comp : Entity_Id) return Boolean
   is
      Ty  : constant Entity_Id :=
        Retysp (if Is_Class_Wide_Type (Rec)
                then Get_Specific_Type_From_Classwide (Rec) else Rec);
   begin
      return Comp_Info (Ty).Visibility (Comp) = Regular
        and then (Ekind (Comp) /= E_Component
                  or else Present (Search_Component_By_Name (Rec, Comp)));
   end Component_Is_Visible_In_Type;

   -------------------------------
   -- Find_Rec_Node_For_Variant --
   -------------------------------

   function Find_Rec_Node_For_Variant (E : Entity_Id) return Entity_Id is
      Ty : constant Entity_Id :=
        Retysp (if Is_Class_Wide_Type (E)
                then Get_Specific_Type_From_Classwide (E) else E);
   begin
      case Ekind (Ty) is

         --  Subtypes do not have their own variant part, rather use the one
         --  from their Etype.

         when E_Record_Subtype
            | E_Record_Subtype_With_Private
            | E_Protected_Subtype
            | E_Task_Subtype
         =>
            return Retysp (Etype (Ty));

         --  Record types always have their own variant part

         when E_Record_Type
            | E_Record_Type_With_Private
         =>
            return Ty;

         --  Concurrent types only have their own variant part if their are
         --  nouveau. If they are derived types, use the variant type of their
         --  Etype.

         when E_Protected_Type
            | E_Task_Type
         =>
            return (if Nkind (Parent (Ty)) in N_Protected_Type_Declaration
                                            | N_Task_Type_Declaration
                    then Ty
                    else Find_Rec_Node_For_Variant (Etype (Ty)));

         when others =>
            return Types.Empty;
      end case;
   end Find_Rec_Node_For_Variant;

   ------------------------
   -- Get_Component_Info --
   ------------------------

   function Get_Component_Info
     (M    : Component_Info_Map;
      Comp : Node_Id)
      return Component_Info
   is (if Nkind (Comp) = N_Defining_Identifier then
          M (Original_Record_Component (Comp))
       else M (Comp));
   --  The variant info map contains bindings for record components and for
   --  variant parts. Only original components are stored.

   -----------------------
   -- Get_Component_Set --
   -----------------------

   function Get_Component_Set (E : Entity_Id) return Node_Sets.Set is
      Ty : constant Entity_Id :=
        Retysp (if Is_Class_Wide_Type (E)
                then Get_Specific_Type_From_Classwide (E) else E);
   begin
      return Comp_Info (Ty).Components;
   end Get_Component_Set;

   ----------------------------------
   -- Get_Component_Visibility_Map --
   ----------------------------------

   function Get_Component_Visibility_Map
     (E : Entity_Id)
      return Component_Visibility_Maps.Map
   is
      Ty : constant Entity_Id :=
        Retysp (if Is_Class_Wide_Type (E)
                then Get_Specific_Type_From_Classwide (E) else E);
   begin
      return Comp_Info (Ty).Visibility;
   end Get_Component_Visibility_Map;

   ------------------------
   -- Get_Descendant_Set --
   ------------------------

   function Get_Descendant_Set (E : Entity_Id) return Node_Sets.Set is
      Ty : constant Entity_Id :=
        Retysp (if Is_Class_Wide_Type (E)
                then Get_Specific_Type_From_Classwide (E) else E);
   begin
      return Descendants (Ty);
   end Get_Descendant_Set;

   ----------------------
   -- Get_Variant_Info --
   ----------------------

   function Get_Variant_Info (E : Entity_Id) return Component_Info_Map is
      Ty : constant Entity_Id := Find_Rec_Node_For_Variant (E);
   begin
      if Present (Ty) then
         return Comp_Info (Ty).Variant_Info;
      else
         return Component_Info_Map'
           (Component_Info_Maps.Empty_Map with null record);
      end if;
   end Get_Variant_Info;

   ----------------------
   -- Has_Private_Part --
   ----------------------

   function Has_Private_Part (E : Entity_Id) return Boolean is
      Ty : constant Entity_Id :=
        Retysp (if Is_Class_Wide_Type (E)
                then Get_Specific_Type_From_Classwide (E) else E);
   begin
      return Comp_Info (Ty).Components.Contains (E);
   end Has_Private_Part;

   ----------------------
   -- Has_Variant_Info --
   ----------------------

   function Has_Variant_Info (Rec, Comp : Entity_Id) return Boolean is
      Rec_Ty  : constant Entity_Id := Find_Rec_Node_For_Variant (Rec);
      C_I_Map : Component_Info_Map renames
        Comp_Info (Rec_Ty).Variant_Info;
      Curs    : constant Component_Info_Maps.Cursor :=
        C_I_Map.Find (Search_Component_In_Type (Rec_Ty, Comp));
   begin
      return Component_Info_Maps.Has_Element (Curs)
        and then Present (C_I_Map (Curs).Parent_Variant);
   end Has_Variant_Info;

   -------------------------
   -- Init_Component_Info --
   -------------------------

   procedure Init_Component_Info
     (E          : Entity_Id;
      Info       : in out Record_Info;
      Visibility : Component_Visibility)
   is

      procedure Mark_Component_List
        (N               : Node_Id;
         Parent_Var_Part : Node_Id;
         Parent_Variant  : Node_Id);

      procedure Mark_Variant_Part
        (N               : Node_Id;
         Parent_Var_Part : Node_Id;
         Parent_Variant  : Node_Id);

      -------------------------
      -- Mark_Component_List --
      -------------------------

      procedure Mark_Component_List
        (N               : Node_Id;
         Parent_Var_Part : Node_Id;
         Parent_Variant  : Node_Id)
      is
         Field : Node_Id := First (Component_Items (N));
      begin
         while Present (Field) loop
            if Nkind (Field) /= N_Pragma then
               Info.Variant_Info.Insert
                 (Defining_Identifier (Field),
                  Component_Info'(
                    Parent_Variant  => Parent_Variant,
                    Parent_Var_Part => Parent_Var_Part));
            end if;
            Next (Field);
         end loop;
         if Present (Variant_Part (N)) then
            Mark_Variant_Part (Variant_Part (N),
                               Parent_Var_Part,
                               Parent_Variant);
         end if;
      end Mark_Component_List;

      -----------------------
      -- Mark_Variant_Part --
      -----------------------

      procedure Mark_Variant_Part
        (N               : Node_Id;
         Parent_Var_Part : Node_Id;
         Parent_Variant  : Node_Id)
      is
         Var : Node_Id := First (Variants (N));

      begin
         Info.Variant_Info.Insert
           (N, Component_Info'(Parent_Variant  => Parent_Variant,
                               Parent_Var_Part => Parent_Var_Part));

         while Present (Var) loop
            Mark_Component_List (Component_List (Var), N, Var);
            Next (Var);
         end loop;
      end Mark_Variant_Part;

      Decl_Node : constant Node_Id := Parent (E);
      Def_Node  : constant Node_Id :=
        (if Nkind (Decl_Node) = N_Full_Type_Declaration
         then Type_Definition (Decl_Node)
         else Types.Empty);

      Discr : Node_Id :=
        (if Nkind (Decl_Node) in N_Full_Type_Declaration
         then First (Discriminant_Specifications (Decl_Node))
         else Types.Empty);

      Components : constant Node_Id :=
        (if Present (Def_Node) then
             (case Nkind (Def_Node) is
                 when N_Record_Definition =>
                    Component_List (Def_Node),
                 when N_Derived_Type_Definition =>
                   (if Present (Record_Extension_Part (Def_Node)) then
                      Component_List (Record_Extension_Part (Def_Node))
                    else Types.Empty),
                 when others =>
                    raise Program_Error)
         else Types.Empty);

      Ancestor_Type : constant Entity_Id := Retysp (Etype (E));

   --  Start of processing for Init_Component_Info

   begin
      while Present (Discr) loop
         Info.Variant_Info.Insert
           (Defining_Identifier (Discr),
            Component_Info'
              (Parent_Variant  => Types.Empty,
               Parent_Var_Part => Types.Empty));
         Next (Discr);
      end loop;

      if Present (Components) then
         Mark_Component_List (Components, Types.Empty, Types.Empty);
      end if;

      --  We only store in Components the first version of a field that we
      --  encounter so that its type is as specialized as possible. If we
      --  are adding a component which has a duplicate in Info.Components,
      --  change its visibility to Duplicated.

      declare
         Comp         : Node_Id := First_Component (E);
         Is_Duplicate : Boolean;
      begin
         while Present (Comp) loop
            if Component_Is_Visible_In_SPARK (Comp)
              and then No
                (Search_Component_In_Info
                   (Info.Components, Comp, Is_Duplicate))
            then
               Info.Components.Insert (Comp);
               pragma Assert (if Is_Duplicate then Visibility /= Regular);
               Info.Visibility.Insert
                 (Comp,
                  (if Visibility = Hidden and then Is_Duplicate then
                        Duplicated
                   else Visibility));
            end if;
            Next_Component (Comp);
         end loop;
      end;

      --  If the type has private fields that are not visible in SPARK, add the
      --  type to the list of components to model these fields.

      if Has_Private_Fields (E) then
         Info.Components.Insert (E);
         Info.Visibility.Insert (E, Hidden);
      end if;

      --  Add components of ancestor types. Components of the ancestor which
      --  are not in E are either Hidden by privacy or Removed by a
      --  discriminant constraint. We assume that components are Removed if
      --  E is constrained and not its ancestor.

      if Ancestor_Type /= E then
         Init_Component_Info
           (Ancestor_Type, Info, Visibility =>
              (if Is_Constrained (E)
                 and then not Is_Constrained (Ancestor_Type)
               then Removed else Hidden));
      end if;
   end Init_Component_Info;

   procedure Init_Component_Info (E : Entity_Id) is
      Position : Component_Info_Map_Maps.Cursor;
      Inserted : Boolean;
   begin
      Comp_Info.Insert (Key      => E,
                        Position => Position,
                        Inserted => Inserted);

      pragma Assert (Inserted);

      --  We can only initialize Variant_Info on new type definitions. For
      --  subtypes, we copy the parent's Components and update the fields
      --  to take the most precise ones from the subtype.

      if Is_Base_Type (E) then
         Init_Component_Info (E, Comp_Info (Position), Visibility => Regular);
      else
         Init_Component_Info_For_Subtypes (E, Comp_Info (Position));
      end if;

      if Is_Tagged_Type (Root_Retysp (E)) then
         Descendants.Include (E, Node_Sets.Empty_Set);
         Store_In_Ancestors (E);
      end if;
   end Init_Component_Info;

   ---------------------------------------------
   -- Init_Component_Info_For_Protected_Types --
   ---------------------------------------------

   procedure Init_Component_Info_For_Protected_Types (E : Entity_Id) is
      Position : Component_Info_Map_Maps.Cursor;
      Inserted : Boolean;
   begin
      Comp_Info.Insert (Key      => E,
                        Position => Position,
                        Inserted => Inserted);

      pragma Assert (Inserted);

      --  We can only initialize Variant_Info on new type definitions. For
      --  subtypes, we copy the parent's Components and update the fields
      --  to take the most precise ones from the subtype.

      if Nkind (Parent (E)) in N_Protected_Type_Declaration
                             | N_Task_Type_Declaration
      then
         declare
            Needs_Private_Part : Boolean := False;
            Field              : Node_Id;
         begin

            --  Init info for discriminants

            if Has_Discriminants (E) then
               Field := First_Discriminant (E);
               while Present (Field) loop
                  Comp_Info (Position).Variant_Info.Insert
                    (Field,
                     Component_Info'(others => Types.Empty));
                  Next_Discriminant (Field);
               end loop;
            end if;

            --  Init info for components

            if Full_View_Not_In_SPARK (E) then
               Needs_Private_Part := True;
            else
               Field := First_Component (E);
               while Present (Field) loop
                  pragma Assert (Component_Is_Visible_In_SPARK (Field));
                  Comp_Info (Position).Variant_Info.Insert
                    (Field,
                     Component_Info'(others => Types.Empty));
                  Comp_Info (Position).Components.Insert (Field);
                  Comp_Info (Position).Visibility.Insert (Field, Regular);
                  Next_Component (Field);
               end loop;
            end if;

            --  Init info for part_of variables

            if Ekind (E) = E_Protected_Type
              and then Is_Single_Concurrent_Type (E)
            then
               for Part of Iter (Part_Of_Constituents (Anonymous_Object (E)))
               loop
                  if Entity_In_SPARK (Part) then
                     Comp_Info (Position).Components.Insert (Part);
                     Comp_Info (Position).Visibility.Insert (Part, Regular);
                  else
                     Needs_Private_Part := True;
                  end if;
               end loop;
            end if;

            if Needs_Private_Part then
               Comp_Info (Position).Components.Insert (E);
               Comp_Info (Position).Visibility.Insert (E, Hidden);
            end if;
         end;
      else
         Init_Component_Info_For_Subtypes (E, Comp_Info (Position));
      end if;
   end Init_Component_Info_For_Protected_Types;

   --------------------------------------
   -- Init_Component_Info_For_Subtypes --
   --------------------------------------

   procedure Init_Component_Info_For_Subtypes
     (E    : Entity_Id;
      Info : in out Record_Info)
   is
   begin
      for C in Get_Component_Visibility_Map (Etype (E)).Iterate loop
         declare
            Field      : Entity_Id renames
              Component_Visibility_Maps.Key (C);
            Visibility : Component_Visibility renames
              Component_Visibility_Maps.Element (C);
            E_Field    : constant Entity_Id :=
              (if Is_Type (Field) then Types.Empty
               else Search_Component_By_Name (E, Field));
         begin

            --  If field is not in E, it must have been removed due to a
            --  discriminant constraint. Copy it to E with visibility Removed.

            if Is_Type (Field) or else No (E_Field) then
               Info.Components.Insert (Field);
               Info.Visibility.Insert
                 (Field,
                  (if Visibility = Regular then Removed else Visibility));
            else
               Info.Components.Insert (E_Field);
               pragma Assert (Visibility = Regular);
               Info.Visibility.Insert (E_Field, Regular);
            end if;
         end;
      end loop;
   end Init_Component_Info_For_Subtypes;

   --------------------------
   -- Original_Declaration --
   --------------------------

   function Original_Declaration (Comp : Entity_Id) return Entity_Id
   is
     (if Is_Type (Comp) then Comp
      elsif Is_Tagged_Type (Retysp (Scope (Comp)))
      then Retysp (Scope (Original_Record_Component (Comp)))
      else Root_Retysp (Scope (Comp)));

   ------------------------------
   -- Search_Component_In_Info --
   ------------------------------

   function Search_Component_In_Info
     (Info         : Node_Sets.Set;
      Comp         : Entity_Id;
      Is_Duplicate : out Boolean)
      return Entity_Id
   is
   begin
      Is_Duplicate := False;

      for Cur_Comp of Info loop
         if Chars (Cur_Comp) = Chars (Comp) then
            Is_Duplicate := True;

            --  We have found a field with the same name. If the type is not
            --  tagged, we have found the correct component. Otherwise, either
            --  it has the same Original_Record_Component and it is the field
            --  we were looking for or it does not and we continue searching.

            if not Is_Tagged_Type (Scope (Comp))
              or else (Is_Type (Comp)
                       and then Is_Type (Cur_Comp)
                       and then Comp = Cur_Comp)
              or else (Ekind (Comp) = E_Component
                       and then Ekind (Cur_Comp) = E_Component
                       and then Original_Record_Component (Cur_Comp) =
                           Original_Record_Component (Comp))
            then
               return Cur_Comp;
            end if;
         end if;
      end loop;
      return Types.Empty;
   end Search_Component_In_Info;

   ------------------------------
   -- Search_Component_In_Type --
   ------------------------------

   function Search_Component_In_Type (Rec, Comp : Entity_Id) return Entity_Id
   is
      Is_Duplicate : Boolean;
   begin
      if Ekind (Comp) = E_Discriminant then
         return Root_Record_Component (Comp);
      else
         pragma Assert (Ekind (Comp) in E_Component | Type_Kind);

         return Search_Component_In_Info
           (Get_Component_Set (Rec), Comp, Is_Duplicate);
      end if;
   end Search_Component_In_Type;

   ------------------------
   -- Store_In_Ancestors --
   ------------------------

   procedure Store_In_Ancestors (E : Entity_Id) is
      Current  : Entity_Id := E;
      Ancestor : Entity_Id;
   begin
      loop
         Ancestor := Retysp (Etype (Current));
         exit when Current = Ancestor;
         Descendants (Ancestor).Insert (E);
         Current := Ancestor;
      end loop;
   end Store_In_Ancestors;

   ----------------------------------
   -- Store_Information_For_Entity --
   ----------------------------------

   procedure Store_Information_For_Entity (E : Entity_Id) is
   begin
      --  Init component information table for E

      if Is_Type (E)
        and then Retysp (E) = E
        and then Ekind (E) in Private_Kind | Record_Kind | Concurrent_Kind
        and then not Is_Class_Wide_Type (E)
      then
         if Is_Concurrent_Type (E) then
            Init_Component_Info_For_Protected_Types (E);
         else
            Init_Component_Info (E);
         end if;
      end if;
   end Store_Information_For_Entity;

end Gnat2Why.Tables;
