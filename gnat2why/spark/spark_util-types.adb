------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                        S P A R K _ U T I L - T Y P E S                   --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                        Copyright (C) 2016-2016, AdaCore                  --
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

with Aspects;                            use Aspects;
with Elists;                             use Elists;
with Flow_Types;                         use Flow_Types;
with Flow_Utility;                       use Flow_Utility;
with Nlists;                             use Nlists;
with Sem_Aux;                            use Sem_Aux;
with Sem_Eval;                           use Sem_Eval;
with SPARK_Definition;                   use SPARK_Definition;
with SPARK_Util.External_Axioms;         use SPARK_Util.External_Axioms;

package body SPARK_Util.Types is

   type Record_Info is record
      Components   : Node_Sets.Set;
      Variant_Info : Info_Maps.Map;
   end record;

   package Info_Map_Maps is new Ada.Containers.Hashed_Maps
     (Key_Type        => Entity_Id,
      Element_Type    => Record_Info,
      Hash            => Node_Hash,
      Equivalent_Keys => "=");

   Comp_Info : Info_Map_Maps.Map := Info_Map_Maps.Empty_Map;
   --  This map maps record types and protected types to a map mapping each
   --  component and each N_Variant node to a Component_Info record. This map
   --  is populated through calls to Init_Component_Info and
   --  Init_Component_Info_For_Protected_Types;

   procedure Init_Component_Info
     (E    : Entity_Id;
      Info : in out Record_Info);
   --  Same as Init_Component_Info (E : Entity_Id) except that information
   --  about E's fields is stored in Info.
   --  @param E record type
   --  @param Info information that should be updated

   function Search_Component_In_Info
     (Info : Node_Sets.Set;
      Comp : Entity_Id)
      return Entity_Id
     with Pre => Ekind (Comp) in E_Component | Type_Kind;

   ---------------------------------------------
   -- Queries related to representative types --
   ---------------------------------------------

   --  This function is similar to Sem_Eval.Is_Static_Subtype, except it only
   --  considers scalar subtypes (otherwise returns False), and looks past
   --  private types.

   -------------------------------
   -- Has_Static_Scalar_Subtype --
   -------------------------------

   function Has_Static_Scalar_Subtype (T : Entity_Id) return Boolean is
      Under_T  : constant Entity_Id := Underlying_Type (T);
      Base_T   : constant Entity_Id := Base_Type (Under_T);
      Anc_Subt : Entity_Id;

   begin
      if not Has_Scalar_Type (Under_T) then
         return False;

      elsif Base_T = Under_T then
         return True;

      else
         Anc_Subt := Ancestor_Subtype (Under_T);

         if Anc_Subt = Empty then
            Anc_Subt := Base_T;
         end if;

         return Has_Static_Scalar_Subtype (Anc_Subt)
           and then Is_Static_Expression (Type_Low_Bound (Under_T))
           and then Is_Static_Expression (Type_High_Bound (Under_T));
      end if;
   end Has_Static_Scalar_Subtype;

   ------------
   -- Retysp --
   ------------

   function Retysp (T : Entity_Id) return Entity_Id is
      Typ : Entity_Id := T;

   begin
      --  Itypes may not be marked. Use their Etype.

      if Is_Itype (Typ) and then not Entity_Marked (Typ) then
         Typ := Etype (Typ);
      end if;

      pragma Assert (Entity_Marked (Typ));

      --  If T is not in SPARK, go through the Partial_View chain to find its
      --  first view in SPARK if any.

      if not Entity_In_SPARK (Typ) then
         loop
            --  If we find a partial view in SPARK, we return it

            if Entity_In_SPARK (Typ) then
               pragma Assert (Full_View_Not_In_SPARK (Typ));
               return Typ;

            --  No partial view in SPARK, return T

            elsif not Entity_Marked (Typ)
              or else not Is_Full_View (Typ)
            then
               return T;

            else
               Typ := Partial_View (Typ);
            end if;
         end loop;

      --  If T is in SPARK but not its most underlying type, then go through
      --  the Full_View chain until the last type in SPARK is found. This code
      --  is largely inspired from the body of Einfo.Underlying_Type.

      elsif Full_View_Not_In_SPARK (Typ) then
         loop
            --  If Full_View (Typ) is in SPARK, use it. Otherwise, we have
            --  found the last type in SPARK in T's chain of Full_View.

            if Present (Full_View (Typ)) then
               if Entity_In_SPARK (Full_View (Typ)) then
                  Typ := Full_View (Typ);
                  pragma Assert (Full_View_Not_In_SPARK (Typ));
               else
                  return Typ;
               end if;

            --  If we have a private type with an underlying full view, either
            --  it is in SPARK and we reach it, or it is not in SPARK and we
            --  return at this point.

            elsif Ekind (Typ) in Private_Kind
              and then Present (Underlying_Full_View (Typ))
            then
               if Entity_In_SPARK (Underlying_Full_View (Typ)) then
                  Typ := Underlying_Full_View (Typ);
                  pragma Assert (Full_View_Not_In_SPARK (Typ));
               else
                  return Typ;
               end if;

            --  If we have an incomplete entity that comes from the limited
            --  view, either its non-limited view is in SPARK and we reach
            --  it, or it is not in SPARK and we return at this point.

            elsif From_Limited_With (Typ)
              and then Present (Non_Limited_View (Typ))
            then
               if Entity_In_SPARK (Non_Limited_View (Typ)) then
                  Typ := Non_Limited_View (Typ);
                  pragma Assert (Full_View_Not_In_SPARK (Typ));
               else
                  return Typ;
               end if;
            else
               return Typ;
            end if;
         end loop;

      --  Otherwise, T's most underlying type is in SPARK, return it.

      else
         loop
            --  If Typ is a private type, reach to its Underlying_Type

            if Is_Private_Type (Typ) then
               Typ := Underlying_Type (Typ);
               pragma Assert (Entity_In_SPARK (Typ));

            --  Otherwise, we've reached T's most underlying type

            else
               return Typ;
            end if;
         end loop;
      end if;
   end Retysp;

   -----------------
   -- Retysp_Kind --
   -----------------

   function Retysp_Kind (T : Entity_Id) return Entity_Kind is
   begin
      return Ekind (Retysp (T));
   end Retysp_Kind;

   ---------------------------------
   -- Has_Visible_Type_Invariants --
   ---------------------------------

   function Has_Visible_Type_Invariants (Ty : Entity_Id) return Boolean is
      Real_Node : constant Node_Id :=
        (if Is_Itype (Ty)
         then Associated_Node_For_Itype (Ty)
         else Ty);

      Main_CU : Entity_Id := Main_Unit_Entity;

   begin
      --  If the current compilation unit is a child unit, go to its parent.

      while Is_Child_Unit (Main_CU) loop
         Main_CU := Unique_Defining_Entity
           (Unit (Enclosing_Lib_Unit_Node (Scope (Main_CU))));
      end loop;
      return Has_Invariants_In_SPARK (Ty) and then
        Unique_Defining_Entity (Unit (Enclosing_Lib_Unit_Node (Real_Node))) =
        Main_CU;
   end Has_Visible_Type_Invariants;

   --------------------------------
   -- Check_Needed_On_Conversion --
   --------------------------------

   function Check_Needed_On_Conversion (From, To : Entity_Id) return Boolean is
      To_R   : constant Entity_Id := Retysp (To);
      From_R : constant Entity_Id := Retysp (From);
   begin
      --  No check needed if same type

      if To_R = From_R then
         return False;

      --  No check needed when converting to base type (for a subtype) or to
      --  parent type (for a derived type).

      elsif To_R = Etype (From_R) then
         return False;

      --  Converting to unconstrained record types does not require a
      --  discriminant check on conversion. The needed check is inserted by the
      --  frontend using an explicit exception.

      --  Converting from a classwide type may require a tag check if the type
      --  to which we convert is not an ancestor.

      --  Converting to a record type with a predicate requires a check.

      elsif Is_Record_Type (To_R)
        and then not (Has_Discriminants (To_R) and then Is_Constrained (To_R))
        and then (not Is_Tagged_Type (To_R) or else Is_Ancestor (To_R, From_R))
        and then not Has_Predicates (To_R)
      then
         return False;

      --  Otherwise a check may be needed

      else
         return True;
      end if;
   end Check_Needed_On_Conversion;

   ----------------------------------
   -- Component_Is_Visible_In_Type --
   ----------------------------------

   function Component_Is_Visible_In_Type (Rec, Comp : Entity_Id) return Boolean
   is
     (Ekind (Comp) in E_Discriminant | E_Component
      and then Present (Search_Component_By_Name (Rec, Comp)));

   ---------------------------------------
   -- Count_Non_Inherited_Discriminants --
   ---------------------------------------

   function Count_Non_Inherited_Discriminants
     (Assocs : List_Id) return Natural
   is
      Association : Node_Id;
      CL          : List_Id;
      Choice      : Node_Id;
      Count       : Natural := 0;

   begin
      Association := Nlists.First (Assocs);
      if No (Association) then
         return 0;
      end if;

      CL := Choices (Association);
      Choice := First (CL);

      while Present (Choice) loop
         if Ekind (Entity (Choice)) = E_Discriminant
           and then not Inherited_Discriminant (Association)
         then
            Count := Count + 1;
         end if;
         Next (Choice);

         if No (Choice) then
            Next (Association);
            if Present (Association) then
               CL := Choices (Association);
               Choice := First (CL);
            end if;
         end if;
      end loop;

      return Count;
   end Count_Non_Inherited_Discriminants;

   ------------------------------
   -- Count_Why_Regular_Fields --
   ------------------------------

   function Count_Why_Regular_Fields (E : Entity_Id) return Natural is
      Count : Natural := Natural (Get_Component_Set (E).Length);

   begin
      --  Add one field for tagged types to represent the unknown extension
      --  components. The field for the tag itself is stored directly in the
      --  Why3 record.

      if Is_Tagged_Type (E) then
         Count := Count + 1;
      end if;

      if Is_Protected_Type (E) then
         for Part of Get_Part_Of_Variables (E) loop
            pragma Unreferenced (Part);
            Count := Count + 1;
         end loop;
      end if;

      return Count;
   end Count_Why_Regular_Fields;

   --------------------------------
   -- Count_Why_Top_Level_Fields --
   --------------------------------

   function Count_Why_Top_Level_Fields (E : Entity_Id) return Natural is
      Count : Natural := 0;

   begin
      --  Store discriminants in a separate sub-record field, so that
      --  subprograms that cannot modify discriminants are passed this
      --  sub-record by copy instead of by reference (with the split version
      --  of the record).

      if Has_Discriminants (E) then
         Count := Count + 1;
      end if;

      --  Store components in a separate sub-record field. This includes:
      --    . visible components of the type
      --    . invisible components and discriminants of a private ancestor
      --    . invisible components of a derived type

      if Count_Why_Regular_Fields (E) > 0 then
         Count := Count + 1;
      end if;

      --  Directly store the attr__constrained and __tag fields in the record,
      --  as these fields cannot be modified after object creation.

      if Has_Defaulted_Discriminants (E) then
         Count := Count + 1;
      end if;

      if Is_Tagged_Type (E) then
         Count := Count + 1;
      end if;

      return Count;
   end Count_Why_Top_Level_Fields;

   ----------------------------
   -- Default_Initialization --
   ----------------------------

   function Default_Initialization
     (Typ           : Entity_Id;
      Explicit_Only : Boolean := False) return Default_Initialization_Kind
   is
      Init : Default_Initialization_Kind;

      FDI : Boolean := False;
      NDI : Boolean := False;
      --  Two flags used to designate whether a record type has at least one
      --  fully default initialized component and/or one not fully default
      --  initialized component.

      function Get_DIC_Pragma (Typ : Entity_Id) return Node_Id
      with Pre => Has_DIC (Typ) or else
                  Has_Inherited_DIC (Typ);
      --  Returns the unanalyzed pragma Default_Initial_Condition applying to a
      --  type.

      procedure Process_Component (Rec_Prot_Comp : Entity_Id);
      --  Process component Rec_Prot_Comp of a record or protected type

      --------------------
      -- Get_DIC_Pragma --
      --------------------

      function Get_DIC_Pragma (Typ : Entity_Id) return Node_Id is
         Par : Entity_Id := Typ;
      begin
         while Has_DIC (Par)
           or else Has_Inherited_DIC (Par)
         loop
            if Has_DIC (Par) then
               return Get_Pragma (Typ, Pragma_Default_Initial_Condition);
            elsif Is_Private_Type (Par) and then Etype (Par) = Par then
               Par := Etype (Full_View (Par));
            else
               Par := Etype (Par);
            end if;
         end loop;

         --  We should not reach here

         raise Program_Error;
      end Get_DIC_Pragma;

      -----------------------
      -- Process_Component --
      -----------------------

      procedure Process_Component (Rec_Prot_Comp : Entity_Id) is
         Comp : Entity_Id := Rec_Prot_Comp;
      begin
         --  The components of discriminated subtypes are not marked as source
         --  entities because they are technically "inherited" on the spot. To
         --  handle such components, use the original record component defined
         --  in the parent type.

         if Present (Original_Record_Component (Comp)) then
            Comp := Original_Record_Component (Comp);
         end if;

         --  Do not process internally generated components except for _parent
         --  which represents the ancestor portion of a derived type.

         if Comes_From_Source (Comp)
           or else Chars (Comp) = Name_uParent
         then
            Init := Default_Initialization (Base_Type (Etype (Comp)),
                                            Explicit_Only);

            --  A component with mixed initialization renders the whole
            --  record/protected type mixed.

            if Init = Mixed_Initialization then
               FDI := True;
               NDI := True;

            --  The component is fully default initialized when its type
            --  is fully default initialized or when the component has an
            --  initialization expression. Note that this has precedence
            --  given that the component type may lack initialization.

            elsif Init = Full_Default_Initialization
              or else Present (Expression (Parent (Comp)))
            then
               FDI := True;

            --  Components with no possible initialization are ignored

            elsif Init = No_Possible_Initialization then
               null;

            --  The component has no full default initialization

            else
               NDI := True;
            end if;
         end if;
      end Process_Component;

      --  Local variables

      Comp   : Entity_Id;
      B_Type : Entity_Id;
      Result : Default_Initialization_Kind;

   --  Start of processing for Default_Initialization

   begin
      --  For types that are not in SPARK we trust the declaration.
      --  This means that if we find a Default_Initial_Condition
      --  aspect we trust it.

      if (not Entity_In_SPARK (Typ)
            or else Full_View_Not_In_SPARK (Typ))
        and then Explicit_Only
      then
         return Default_Initialization (Typ);
      end if;

      --  For some subtypes we have to check for attributes
      --  Has_DIC and Has_Inherited_DIC on
      --  the base type instead. However, we want to skip Itypes while
      --  doing so.

      B_Type := Typ;
      if Ekind (B_Type) in Subtype_Kind then
         while (Ekind (B_Type) in Subtype_Kind
                  or else Is_Itype (B_Type))

           --  Stop if we find either of the attributes
           and then not (Has_DIC (B_Type)
                           or else Has_Inherited_DIC (B_Type))

           --  Stop if we cannot make any progress
           and then not Is_Nouveau_Type (B_Type)
         loop
            B_Type := Etype (B_Type);
         end loop;
      end if;

      --  If we are considering implicit initializations and
      --  Default_Initial_Condition was specified for the type, take
      --  it into account.

      if not Explicit_Only
        and then (Has_DIC (B_Type)
                    or else Has_Inherited_DIC (B_Type))
      then
         declare
            Prag : constant Node_Id := Get_DIC_Pragma (B_Type);
            Expr : Node_Id;
         begin
            --  The pragma has an argument. If NULL, this indicates a value of
            --  the type is not default initialized. Otherwise, a value of the
            --  type should be fully default initialized.

            if Present (Prag) and then
              Present (Pragma_Argument_Associations (Prag))
            then
               Expr :=
                 Get_Pragma_Arg (First (Pragma_Argument_Associations (Prag)));

               if Nkind (Expr) = N_Null then
                  Result := No_Default_Initialization;
               else
                  Result := Full_Default_Initialization;
               end if;

            --  Otherwise the pragma appears without an argument, indicating
            --  a value of the type if fully default initialized.

            else
               Result := Full_Default_Initialization;
            end if;
         end;

      --  Access types are always fully default initialized

      elsif Is_Access_Type (Typ) then
         Result := Full_Default_Initialization;

      --  The initialization status of a private type depends on its full view

      elsif Is_Private_Type (Typ) and then Present (Full_View (Typ)) then
         Result := Default_Initialization (Full_View (Typ), Explicit_Only);

      --  A scalar type subject to aspect/pragma Default_Value is
      --  fully default initialized.

      elsif Is_Scalar_Type (Typ)
        and then Is_Scalar_Type (Base_Type (Typ))
        and then Present (Default_Aspect_Value (Base_Type (Typ)))
      then
         Result := Full_Default_Initialization;

      --  A scalar type whose base type is private may still be subject to
      --  aspect/pragma Default_Value, so it depends on the base type.

      elsif Is_Scalar_Type (Typ)
        and then Is_Private_Type (Base_Type (Typ))
      then
         Result := Default_Initialization (Base_Type (Typ), Explicit_Only);

      --  Task types are always fully default initialized

      elsif Is_Task_Type (Typ) then
         Result := Full_Default_Initialization;

      --  A derived type is only initialized if its base type and any
      --  extensions that it defines are fully default initialized.

      elsif Is_Derived_Type (Typ) then
         declare
            Type_Def : Node_Id := Empty;
            Rec_Part : Node_Id := Empty;

         begin
            --  If Typ is an Itype, it may not have an Parent field pointing to
            --  a corresponding declaration. In that case, there is no record
            --  extension part to check for default initialization. Similarly,
            --  if the corresponding declaration is not a full type declaration
            --  for a derived type definition, there is no extension part to
            --  check.

            if Present (Parent (Typ))
              and then Nkind (Parent (Typ)) = N_Full_Type_Declaration
            then
               Type_Def := Type_Definition (Parent (Typ));
               if Nkind (Type_Def) = N_Derived_Type_Definition then
                  Rec_Part := Record_Extension_Part (Type_Def);
               end if;
            end if;

            if Present (Rec_Part)
              and then not Null_Present (Rec_Part)
            then
               --  When the derived type has extensions we check both
               --  the base type and the extensions.
               declare
                  Base_Initialized : Default_Initialization_Kind;
                  Ext_Initialized  : Default_Initialization_Kind;
               begin
                  Base_Initialized :=
                    Default_Initialization (Etype (Typ),
                                            Explicit_Only);

                  if Is_Tagged_Type (Typ) then
                     Comp := First_Non_Pragma
                       (Component_Items (Component_List (Rec_Part)));
                  else
                     Comp := First_Non_Pragma (Component_Items (Rec_Part));
                  end if;

                  --  Inspect all components of the extension

                  if Present (Comp) then
                     while Present (Comp) loop
                        if Ekind (Defining_Identifier (Comp)) = E_Component
                        then
                           Process_Component (Defining_Identifier (Comp));
                        end if;

                        Next_Non_Pragma (Comp);
                     end loop;

                     --  Detect a mixed case of initialization

                     if FDI and NDI then
                        Ext_Initialized := Mixed_Initialization;

                     elsif FDI then
                        Ext_Initialized := Full_Default_Initialization;

                     elsif NDI then
                        Ext_Initialized := No_Default_Initialization;

                      --  The type either has no components or they
                      --  are all internally generated. The extensions
                      --  are trivially fully default initialized

                     else
                        Ext_Initialized := Full_Default_Initialization;
                     end if;

                  --  The extension is null, there is nothing to
                  --  initialize.

                  else
                     if Explicit_Only then
                        --  The extensions are trivially fully default
                        --  initialized.
                        Ext_Initialized := Full_Default_Initialization;
                     else
                        Ext_Initialized := No_Possible_Initialization;
                     end if;
                  end if;

                  if Base_Initialized = Full_Default_Initialization
                    and then Ext_Initialized = Full_Default_Initialization
                  then
                     Result := Full_Default_Initialization;
                  else
                     Result := No_Default_Initialization;
                  end if;
               end;
            else
               Result := Default_Initialization (Etype (Typ),
                                                 Explicit_Only);
            end if;
         end;

      --  An array type subject to aspect/pragma Default_Component_Value is
      --  fully default initialized. Otherwise its initialization status is
      --  that of its component type.

      elsif Is_Array_Type (Typ) then
         if Present (Default_Aspect_Component_Value
                     (if Is_Partial_View (Base_Type (Typ))
                        then Full_View (Base_Type (Typ))
                        else Base_Type (Typ)))
         then
            Result := Full_Default_Initialization;
         else
            Result := Default_Initialization (Component_Type (Typ),
                                              Explicit_Only);
         end if;

      --  Record types and protected types offer several initialization options
      --  depending on their components (if any).

      elsif Is_Record_Type (Typ) or else Is_Protected_Type (Typ) then
         Comp := First_Entity (Typ);

         --  Inspect all components

         if Present (Comp) then
            while Present (Comp) loop
               if Ekind (Comp) = E_Component then
                  Process_Component (Comp);
               end if;

               Next_Entity (Comp);
            end loop;

            --  Detect a mixed case of initialization

            if FDI and NDI then
               Result := Mixed_Initialization;

            elsif FDI then
               Result := Full_Default_Initialization;

            elsif NDI then
               Result := No_Default_Initialization;

            --  The type either has no components or they are all
            --  internally generated.

            else
               if Explicit_Only then
                  --  The record is considered to be trivially fully
                  --  default initialized.
                  Result := Full_Default_Initialization;
               else
                  Result := No_Possible_Initialization;
               end if;
            end if;

         --  The type is null, there is nothing to initialize.

         else
            if Explicit_Only then
               --  We consider the record to be trivially fully
               --  default initialized.
               Result := Full_Default_Initialization;
            else
               Result := No_Possible_Initialization;
            end if;
         end if;

      --  The type has no default initialization

      else
         Result := No_Default_Initialization;
      end if;

      --  In specific cases, we'd rather consider the type as having no
      --  default initialization (which is allowed in SPARK) rather than
      --  mixed initialization (which is not allowed).

      if Result = Mixed_Initialization then

         --  If the type is one for which an external axiomatization
         --  is provided, it is fine if the implementation uses mixed
         --  initialization. This is the case for formal containers in
         --  particular.

         if Type_Based_On_Ext_Axioms (Typ) then
            Result := No_Default_Initialization;

         --  If the type is private or class wide, it is fine if the
         --  implementation uses mixed initialization. An error will be issued
         --  when analyzing the implementation if it is in a SPARK part of the
         --  code.

         elsif Is_Private_Type (Typ) or else Is_Class_Wide_Type (Typ) then
            Result := No_Default_Initialization;
         end if;
      end if;

      return Result;
   end Default_Initialization;

   ---------------------------
   -- Find_Predicate_Aspect --
   ---------------------------

   function Find_Predicate_Aspect (Typ : Entity_Id) return Node_Id is
      N : Node_Id;

   begin
      N := Find_Aspect (Typ, Aspect_Predicate);
      if Present (N) then
         return N;
      end if;

      N := Find_Aspect (Typ, Aspect_Dynamic_Predicate);
      if Present (N) then
         return N;
      end if;

      N := Find_Aspect (Typ, Aspect_Static_Predicate);
      return N;
   end Find_Predicate_Aspect;

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

   ------------------------------------
   -- Get_Full_Type_Without_Checking --
   ------------------------------------

   function Get_Full_Type_Without_Checking (N : Node_Id) return Entity_Id is
      T : constant Entity_Id := Etype (N);
   begin
      if Nkind (N) in N_Entity and then Ekind (N) = E_Abstract_State then
         return T;
      else
         pragma Assert (Is_Type (T));
         if Present (Full_View (T)) then
            return Full_View (T);
         else
            return T;
         end if;
      end if;
   end Get_Full_Type_Without_Checking;

   ---------------------------------
   -- Get_Iterable_Type_Primitive --
   ---------------------------------

   function Get_Iterable_Type_Primitive
     (Typ : Entity_Id;
      Nam : Name_Id) return Entity_Id
     is (Ultimate_Alias (Sem_Util.Get_Iterable_Type_Primitive (Typ, Nam)));

   --------------------------------------
   -- Get_Specific_Type_From_Classwide --
   --------------------------------------

   function Get_Specific_Type_From_Classwide (E : Entity_Id) return Entity_Id
   is
      S : constant Entity_Id :=
        (if Ekind (E) = E_Class_Wide_Subtype then Etype (Etype (E))
         else Etype (E));
   begin
      if Is_Full_View (S) then
         return Partial_View (S);
      else
         return S;
      end if;
   end Get_Specific_Type_From_Classwide;

   -------------------------------------
   -- Get_Stored_Constraint_For_Discr --
   -------------------------------------

   function Get_Stored_Constraint_For_Discr
     (Ty    : Entity_Id;
      Discr : Entity_Id)
      return Node_Id
   is
      Current : Entity_Id := First_Discriminant (Ty);
      Elmt    : Elmt_Id := First_Elmt (Stored_Constraint (Ty));
   begin
      while Current /= Discr loop
         Current := Next_Discriminant (Current);
         Elmt := Next_Elmt (Elmt);
      end loop;
      return Node (Elmt);
   end Get_Stored_Constraint_For_Discr;

   ----------------------
   -- Get_Variant_Info --
   ----------------------

   function Get_Variant_Info (E : Entity_Id) return Info_Maps.Map is
      Ty : constant Entity_Id := Retysp (E);
   begin
      case Ekind (Ty) is
         when E_Record_Subtype
            | E_Record_Subtype_With_Private
         =>
            return Comp_Info (Retysp (Etype (Ty))).Variant_Info;
         when E_Record_Type
            | E_Record_Type_With_Private
            | Concurrent_Kind
         =>
            return Comp_Info (Ty).Variant_Info;
         when others =>
            return Info_Maps.Empty_Map;
      end case;
   end Get_Variant_Info;

   ------------------------------
   -- Has_Invariants_In_SPARK --
   -----------------------------

   function Has_Invariants_In_SPARK (E : Entity_Id) return Boolean is
     (Has_Own_Invariants (E)
      and then Ekind (E) not in Subtype_Kind
      and then (if Is_Partial_View (E) then Entity_In_SPARK (Full_View (E))));

   ----------------------------------
   -- Has_Private_Ancestor_Or_Root --
   ----------------------------------

   function Has_Private_Ancestor_Or_Root (E : Entity_Id) return Boolean is
      Ancestor : Entity_Id := E;
   begin
      if not Is_Tagged_Type (E) then
         return False;
      end if;

      if Has_Private_Ancestor (E) then
         return True;
      end if;

      if not Full_View_Not_In_SPARK (E) then
         return False;
      end if;

      --  Go to the first new type in E's hierarchy

      while Ekind (Ancestor) in Subtype_Kind loop
         pragma Assert (Full_View_Not_In_SPARK (Ancestor));
         pragma Assert (Ancestor /= Get_First_Ancestor_In_SPARK (Ancestor));
         Ancestor := Get_First_Ancestor_In_SPARK (Ancestor);
      end loop;

      --  Return True if it has an ancestor whose fullview is not in SPARK

      return Get_First_Ancestor_In_SPARK (Ancestor) /= Ancestor
        and then Full_View_Not_In_SPARK
          (Get_First_Ancestor_In_SPARK (Ancestor));
   end Has_Private_Ancestor_Or_Root;

   ------------------------
   -- Has_Private_Fields --
   ------------------------

   function Has_Private_Fields (E : Entity_Id) return Boolean is
      Ty : constant Entity_Id := Retysp (E);
   begin
      if not Full_View_Not_In_SPARK (Ty) then
         return False;
      end if;

      --  Subtypes don't have private fields of their own.

      if Ekind (Ty) in Subtype_Kind then
         return False;
      end if;

      --  Derived non-tagged types cannot have private fields of their own.

      if not Is_Tagged_Type (Ty)
        and then Get_First_Ancestor_In_SPARK (Ty) /= Ty
      then
         return False;
      end if;

      --  Return True if Ty is a private type

      return Ekind (Ty) in Private_Kind;
   end Has_Private_Fields;

   -----------------------------------
   -- Has_Static_Discrete_Predicate --
   -----------------------------------

   function Has_Static_Discrete_Predicate (E : Entity_Id) return Boolean is
     (Is_Discrete_Type (E)
        and then Has_Predicates (E)
        and then Present (Static_Discrete_Predicate (E)));

   -------------------------
   -- Init_Component_Info --
   -------------------------

   procedure Init_Component_Info
     (E    : Entity_Id;
      Info : in out Record_Info)
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
         else Empty);

      Discr : Node_Id :=
        (if Nkind (Decl_Node) in N_Full_Type_Declaration
         then First (Discriminant_Specifications (Decl_Node))
         else Empty);

      Components : constant Node_Id :=
        (if Present (Def_Node) then
             (case Nkind (Def_Node) is
                 when N_Record_Definition =>
                    Component_List (Def_Node),
                 when N_Derived_Type_Definition =>
                   (if Present (Record_Extension_Part (Def_Node)) then
                      Component_List (Record_Extension_Part (Def_Node))
                    else Empty),
                 when others =>
                    raise Program_Error)
         else Empty);

      Ancestor_Type : constant Entity_Id :=
        (if Full_View_Not_In_SPARK (E) then Get_First_Ancestor_In_SPARK (E)
         else Retysp (Etype (E)));

   --  Start of processing for Init_Component_Info

   begin
      while Present (Discr) loop
         Info.Variant_Info.Insert
           (Defining_Identifier (Discr),
            Component_Info'
              (Parent_Variant  => Empty,
               Parent_Var_Part => Empty));
         Next (Discr);
      end loop;

      if Present (Components) then
         Mark_Component_List (Components, Empty, Empty);
      end if;

      --  We only store in Components the first version of a field that we
      --  encounter so that its type is as specialized as possible.

      declare
         Comp : Node_Id := First_Component (E);
      begin
         while Present (Comp) loop
            if Component_Is_Visible_In_SPARK (Comp)
              and then No (Search_Component_In_Info (Info.Components, Comp))
            then
               Info.Components.Insert (Comp);
            end if;
            Next_Component (Comp);
         end loop;
      end;

      --  If the type has private fields that are not visible in SPARK, add the
      --  type to the list of components to model these fields.

      if Has_Private_Fields (E) then
         Info.Components.Insert (E);
      end if;

      --  Add components of ancestor types.

      if Ancestor_Type /= E then
         Init_Component_Info (Ancestor_Type, Info);
      end if;
   end Init_Component_Info;

   procedure Init_Component_Info (E : Entity_Id) is
      Position : Info_Map_Maps.Cursor;
      Inserted : Boolean;
   begin
      Comp_Info.Insert (Key      => E,
                        Position => Position,
                        Inserted => Inserted);

      pragma Assert (Inserted);

      --  We can only initialize Variant_Info on new type definitions. For
      --  subtypes, we copy the parent's Components and update the fields
      --  to take the most precise ones from the subtype.

      if Ekind (E) in Subtype_Kind then
         for Field of Get_Component_Set (Etype (E)) loop

            --  If field is hidden in Etype (E), copy it to E

            if Ekind (Field) in Type_Kind
              or else No (Search_Component_By_Name (E, Field))
            then
               Comp_Info (Position).Components.Insert (Field);
            else
               Comp_Info (Position).Components.Insert
                 (Search_Component_By_Name (E, Field));
            end if;
         end loop;
      else
         Init_Component_Info (E, Comp_Info (Position));
      end if;
   end Init_Component_Info;

   ---------------------------------------------
   -- Init_Component_Info_For_Protected_Types --
   ---------------------------------------------

   procedure Init_Component_Info_For_Protected_Types (E : Entity_Id) is
      Info  : Info_Maps.Map;
      Comps : Node_Sets.Set;
      Field : Entity_Id := First_Entity (E);
   begin
      while Present (Field) loop
         if Ekind (Field) in E_Discriminant | E_Component then
            Info.Insert
              (Field,
               Component_Info'(others => Empty));

            if Ekind (Field) = E_Component then
               pragma Assert (Component_Is_Visible_In_SPARK (Field));
               Comps.Insert (Field);
            end if;
         end if;

         Next_Entity (Field);
      end loop;

      if Has_Private_Fields (E) then
         Comps.Insert (E);
      end if;

      Comp_Info.Insert (E, (Variant_Info => Info, Components => Comps));
   end Init_Component_Info_For_Protected_Types;

   ------------------------------
   -- Invariant_Check_Needed --
   ------------------------------

   function Invariant_Check_Needed (Ty : Entity_Id) return Boolean
   is
      Rep_Ty  : constant Entity_Id := Retysp (Ty);
      Current : Entity_Id := Rep_Ty;
      Parent  : Entity_Id;

   begin
      --  Check for invariants on the type and its ancestors

      loop
         if Has_Visible_Type_Invariants (Current) then
            return True;
         end if;

         if Full_View_Not_In_SPARK (Current) then
            Parent := Get_First_Ancestor_In_SPARK (Current);
         else
            Parent := Retysp (Etype (Current));
         end if;
         exit when Current = Parent;
         Current := Parent;
      end loop;

      --  Check for invariants on components.

      if Is_Array_Type (Rep_Ty) then
         return Invariant_Check_Needed (Component_Type (Rep_Ty));

      elsif Is_Private_Type (Rep_Ty)
        or else Is_Record_Type (Rep_Ty)
        or else Is_Concurrent_Type (Rep_Ty)
      then
         if Has_Discriminants (Rep_Ty) then
            declare
               Discr : Entity_Id := First_Discriminant (Rep_Ty);
            begin
               while Present (Discr) loop
                  if Invariant_Check_Needed (Etype (Discr)) then
                     return True;
                  end if;

                  Discr := Next_Discriminant (Discr);
               end loop;
            end;
         end if;

         for Comp of Get_Component_Set (Rep_Ty) loop
            if Ekind (Comp) = E_Component
              and then Invariant_Check_Needed (Etype (Comp))
            then
               return True;
            end if;
         end loop;
      end if;
      return False;
   end Invariant_Check_Needed;

   -------------------
   -- Is_Null_Range --
   -------------------

   function Is_Null_Range (T : Entity_Id) return Boolean is
     (Is_Discrete_Type (T)
      and then Has_Static_Scalar_Subtype (T)
      and then Expr_Value (Low_Bound (Scalar_Range (T))) >
          Expr_Value (High_Bound (Scalar_Range (T))));

   ------------------------------
   -- Is_Standard_Boolean_Type --
   ------------------------------

   function Is_Standard_Boolean_Type (E : Entity_Id) return Boolean is
     (E = Standard_Boolean
      or else
        (Ekind (E) = E_Enumeration_Subtype
         and then Etype (E) = Standard_Boolean
        and then Scalar_Range (E) = Scalar_Range (Standard_Boolean)));

   --------------------------
   -- Is_Static_Array_Type --
   --------------------------

   function Is_Static_Array_Type (E : Entity_Id) return Boolean is
     (Is_Array_Type (E)
        and then Is_Constrained (E)
        and then Has_Static_Array_Bounds (E));

   ---------------------
   -- Needs_DIC_Check --
   ---------------------

   function Needs_DIC_Check (Ty : Entity_Id) return Boolean is
      E   : Entity_Id := Ty;
      Old : Entity_Id;

   begin
      --  Search for the type holding the DIC to see if it is a private type

      while Full_View_Not_In_SPARK (E)
        and then Has_Inherited_DIC (E)
      loop
         Old := E;
         E := Get_First_Ancestor_In_SPARK (E);
         pragma Assert (Old /= E);
      end loop;

      --  Either we have found the type holding the DIC or we have found a type
      --  whose fullview is in SPARK. In the first case, we need a check only
      --  if E is not a private type.

      return Has_Inherited_DIC (E)
        or else (Has_DIC (E) and then not Has_Private_Type (E));
   end Needs_DIC_Check;

   --------------------
   -- Nth_Index_Type --
   --------------------

   function Nth_Index_Type (E : Entity_Id; Dim : Positive) return Node_Id is
      Cur   : Positive := 1;
      Index : Node_Id := First_Index (E);

   begin
      if Ekind (E) = E_String_Literal_Subtype then
         pragma Assert (Dim = 1);
         return E;
      end if;

      while Cur /= Dim loop
         Cur := Cur + 1;
         Next_Index (Index);
      end loop;

      return Etype (Index);
   end Nth_Index_Type;

   --------------------------
   -- Original_Declaration --
   --------------------------

   function Original_Declaration (Comp : Entity_Id) return Entity_Id
   is
     (if Ekind (Comp) in Type_Kind then Comp
      elsif Is_Tagged_Type (Retysp (Scope (Comp)))
      then Retysp (Scope (Original_Record_Component (Comp)))
      else Root_Record_Type (Scope (Comp)));

   ---------------------------------------
   -- Private_Declarations_Of_Prot_Type --
   ---------------------------------------

   function Private_Declarations_Of_Prot_Type (E : Entity_Id) return List_Id
   is (Private_Declarations (Protected_Type_Definition (Base_Type (E))));

   ---------------------------------------
   -- Private_Declarations_Of_Task_Type --
   ---------------------------------------

   function Private_Declarations_Of_Task_Type (E : Entity_Id) return List_Id
   is
      Def : constant Node_Id := Task_Type_Definition (E);
   begin
      if Present (Def) then
         return Private_Declarations (Def);
      else
         return Empty_List;
      end if;
   end Private_Declarations_Of_Task_Type;

   --------------------
   -- Protected_Body --
   --------------------

   function Protected_Body (E : Entity_Id) return Node_Id is
      Ptr : constant Node_Id := Parent (E);

   begin
      pragma Assert (Nkind (Ptr) = N_Protected_Type_Declaration);
      return Parent (Corresponding_Body (Ptr));
   end Protected_Body;

   -------------------------------
   -- Protected_Type_Definition --
   -------------------------------

   function Protected_Type_Definition (E : Entity_Id) return Node_Id is
      Decl : constant Node_Id := Parent (E);
      pragma Assert (Nkind (Decl) = N_Protected_Type_Declaration);

   begin
      return Protected_Definition (Decl);
   end Protected_Type_Definition;

   ---------------------------------
   -- Requires_Interrupt_Priority --
   ---------------------------------

   function Requires_Interrupt_Priority (E : Entity_Id) return Boolean is

      function Decl_Has_Attach_Handler (Decl : Node_Id) return Boolean;
      --  Check whether the declaration is a subprogram with an attach_handler
      --  pragma attached.

      -----------------------------
      -- Decl_Has_Attach_Handler --
      -----------------------------

      function Decl_Has_Attach_Handler (Decl : Node_Id) return Boolean is
      begin
         return
           Nkind (Decl) in N_Subprogram_Declaration
                         | N_Abstract_Subprogram_Declaration
           and then Present (Get_Pragma (Defining_Entity (Decl),
                                         Pragma_Attach_Handler));
      end Decl_Has_Attach_Handler;

      Decls : List_Id := Visible_Declarations_Of_Prot_Type (E);
      Decl  : Node_Id := First (Decls);

   --  Start of processing for Requires_Interrupt_Priority

   begin
      while Present (Decl) loop
         if Decl_Has_Attach_Handler (Decl) then
            return True;
         end if;
         Next (Decl);
      end loop;
      if Private_Spec_In_SPARK (E) then
         Decls := Private_Declarations_Of_Prot_Type (E);
         Decl := First (Decls);
         while Present (Decl) loop
            if Decl_Has_Attach_Handler (Decl) then
               return True;
            end if;
            Next (Decl);
         end loop;
      end if;
      return False;
   end Requires_Interrupt_Priority;

   ----------------------
   -- Root_Record_Type --
   ----------------------

   function Root_Record_Type (E : Entity_Id) return Entity_Id is
      Result   : Entity_Id := Empty;
      Ancestor : Entity_Id :=
        (if Is_Class_Wide_Type (E) then Get_Specific_Type_From_Classwide (E)
         else E);
   begin
      --  Climb the type derivation chain with Root_Type, applying
      --  Underlying_Type or Get_First_Ancestor_In_SPARK to pass private type
      --  boundaries.

      --  ??? this code requires comments

      while Ancestor /= Result loop

         Result := Ancestor;
         Ancestor := Root_Type (Result);

         if Full_View_Not_In_SPARK (Ancestor) then
            Ancestor := Get_First_Ancestor_In_SPARK (Ancestor);
         else
            Ancestor := Underlying_Type (Ancestor);
         end if;
      end loop;

      return Retysp (Result);
   end Root_Record_Type;

   ------------------------------
   -- Search_Component_In_Info --
   ------------------------------

   function Search_Component_In_Info
     (Info : Node_Sets.Set;
      Comp : Entity_Id)
       return Entity_Id
   is
   begin
      for Cur_Comp of Info loop
         if Chars (Cur_Comp) = Chars (Comp) then

            --  We have found a field with the same name. If the type is not
            --  tagged, we have found the correct component. Otherwise, either
            --  it has the same Original_Record_Component and it is the field
            --  we were looking for or it does not and we continue searching.

            if not Is_Tagged_Type (Scope (Comp))
              or else (Ekind (Comp) in Type_Kind
                       and then Ekind (Cur_Comp) in Type_Kind
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
      return Empty;
   end Search_Component_In_Info;

   ------------------------------
   -- Search_Component_In_Type --
   ------------------------------

   function Search_Component_In_Type (Rec, Comp : Entity_Id) return Entity_Id
   is
   begin
      if Ekind (Comp) = E_In_Parameter then

         return Search_Component_By_Name (Rec, Comp);
      elsif Ekind (Comp) = E_Discriminant then
         return Root_Record_Component (Comp);
      else
         pragma Assert (Ekind (Comp) in E_Component | Type_Kind);

         return Search_Component_In_Info (Get_Component_Set (Rec), Comp);
      end if;
   end Search_Component_In_Type;

   -------------------------
   -- Static_Array_Length --
   -------------------------

   function Static_Array_Length (E : Entity_Id; Dim : Positive) return Uint is
   begin
      if Ekind (E) = E_String_Literal_Subtype then
         return String_Literal_Length (E);
      else
         declare
            F_Index : constant Entity_Id := Nth_Index_Type (E, Dim);

            Rng   : constant Node_Id := Get_Range (F_Index);
            First : constant Uint := Expr_Value (Low_Bound (Rng));
            Last  : constant Uint := Expr_Value (High_Bound (Rng));
         begin
            if Last >= First then
               return Last - First + Uint_1;
            else
               return Uint_0;
            end if;
         end;
      end if;
   end Static_Array_Length;

   ---------------
   -- Task_Body --
   ---------------

   function Task_Body (E : Entity_Id) return Node_Id is
      Ptr : constant Node_Id := Parent (E);
   begin
      pragma Assert (Nkind (Ptr) = N_Task_Type_Declaration);
      return Parent (Corresponding_Body (Ptr));
   end Task_Body;

   ----------------------
   -- Task_Body_Entity --
   ----------------------

   function Task_Body_Entity (E : Entity_Id) return Entity_Id is
      T_Body : constant Node_Id := Task_Body (E);
   begin
      if Present (T_Body) then
         pragma Assert (Present (Defining_Identifier (T_Body)));
         return Defining_Identifier (T_Body);
      else
         return Empty;
      end if;
   end Task_Body_Entity;

   ---------------------------------------
   -- Visible_Declarations_Of_Prot_Type --
   ---------------------------------------

   function Visible_Declarations_Of_Prot_Type (E : Entity_Id) return List_Id
   is (Visible_Declarations (Protected_Type_Definition (Base_Type (E))));

   ---------------------------------------
   -- Visible_Declarations_Of_Task_Type --
   ---------------------------------------

   function Visible_Declarations_Of_Task_Type (E : Entity_Id) return List_Id
   is
      Def : constant Node_Id := Task_Type_Definition (E);
   begin
      if Present (Def) then
         return Visible_Declarations (Def);
      else
         return Empty_List;
      end if;
   end Visible_Declarations_Of_Task_Type;

end SPARK_Util.Types;
