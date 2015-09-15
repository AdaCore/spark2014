------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                            S P A R K _ U T I L                           --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                        Copyright (C) 2011-2015, AdaCore                  --
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

with Ada.Strings;                        use Ada.Strings;
with Ada.Strings.Equal_Case_Insensitive;
with Ada.Strings.Unbounded;              use Ada.Strings.Unbounded;
with Assumption_Types;                   use Assumption_Types;
with Csets;                              use Csets;
with Gnat2Why.Assumptions;               use Gnat2Why.Assumptions;
with Gnat2Why_Args;
with GNATCOLL.Utils;                     use GNATCOLL.Utils;
with Exp_Util;                           use Exp_Util;
with Flow_Types;                         use Flow_Types;
with Flow_Utility;                       use Flow_Utility;
with Fname;                              use Fname;
with Nlists;                             use Nlists;
with Pprint;                             use Pprint;
with Sem_Aux;                            use Sem_Aux;
with Sem_Disp;                           use Sem_Disp;
with Sem_Eval;                           use Sem_Eval;
with SPARK_Definition;                   use SPARK_Definition;
with Stringt;                            use Stringt;
with Treepr;                             use Treepr;
with Urealp;                             use Urealp;
with VC_Kinds;                           use VC_Kinds;
with Sem_Ch12;                           use Sem_Ch12;

package body SPARK_Util is

   function Is_Main_Cunit (N : Node_Id) return Boolean;
   function Is_Spec_Unit_Of_Main_Unit (N : Node_Id) return Boolean;

   ------------------------------
   -- Extra tables on entities --
   ------------------------------

   Partial_Views : Node_Maps.Map;
   --  Map from full views of entities to their partial views, for deferred
   --  constants and private types.

   procedure Set_Partial_View (E, V : Entity_Id) is
   begin
      Partial_Views.Insert (E, V);
   end Set_Partial_View;

   function Partial_View (E : Entity_Id) return Entity_Id is
      (if Partial_Views.Contains (E) then
         Partial_Views.Element (E)
       else Empty);

   function Is_Full_View (E : Entity_Id) return Boolean is
      (Present (Partial_View (E)));

   function Is_Partial_View (E : Entity_Id) return Boolean is
     ((Is_Type (E) or else Ekind (E) = E_Constant) and then
      Present (Full_View (E)));

   Specific_Tagged_Types : Node_Maps.Map;
   --  Map from classwide types to the corresponding specific tagged type

   procedure Set_Specific_Tagged (E, V : Entity_Id) is
   begin
      if Is_Full_View (V)
        and then Full_View_Not_In_SPARK (Partial_View (V))
      then
         Specific_Tagged_Types.Insert (E, Partial_View (V));
      else
         Specific_Tagged_Types.Insert (E, V);
      end if;
   end Set_Specific_Tagged;

   function Specific_Tagged (E : Entity_Id) return Entity_Id is
     (Specific_Tagged_Types.Element (E));

   ------------------------------------------------
   -- Queries related to external axiomatization --
   ------------------------------------------------

   function Entity_In_Ext_Axioms (E : Entity_Id) return Boolean is
     (Present (Containing_Package_With_Ext_Axioms (E)));

   function Is_Access_To_Ext_Axioms_Discriminant
     (N : Node_Id) return Boolean
   is
      E : constant Entity_Id := Entity (Selector_Name (N));
   begin
      return Ekind (E) = E_Discriminant
        and then Is_Ext_Axioms_Discriminant (E);
   end Is_Access_To_Ext_Axioms_Discriminant;

   function Is_Ext_Axioms_Discriminant (E : Entity_Id) return Boolean is
      Typ : constant Entity_Id :=
        Unique_Defining_Entity (Enclosing_Declaration (E));
   begin
      return Type_Based_On_Ext_Axioms (Etype (Typ));
   end Is_Ext_Axioms_Discriminant;

   function Package_Has_Ext_Axioms (E : Entity_Id) return Boolean is
      (Has_Annotate_Pragma_For_External_Axiomatization (E));

   function Type_Based_On_Ext_Axioms (E : Entity_Id) return Boolean is
     (Present (Underlying_Ext_Axioms_Type (E)));

   function Underlying_Ext_Axioms_Type (E : Entity_Id) return Entity_Id is
      Typ : Entity_Id := E;
   begin
      loop
         --  Return Typ if it is a private type defined in a package with
         --  external axiomatization.

         if Is_Private_Type (Typ)
           and then Entity_In_Ext_Axioms (Typ)
         then
            return Typ;
         end if;

         --  If Typ is a nouveau type, there is no possible parent type or base
         --  type from a package with external axiomatization. Return Empty.

         if Is_Nouveau_Type (Typ) then
            return Empty;
         end if;

         --  Otherwise, use Etype to reach to the parent type for a derived
         --  type, or the base type for a subtype.

         Typ := Etype (Typ);
      end loop;
   end Underlying_Ext_Axioms_Type;

   ---------------------------------------------
   -- Queries related to representative types --
   ---------------------------------------------

   --  This function is similar to Sem_Eval.Is_Static_Subtype, except it only
   --  considers scalar subtypes (otherwise returns False), and looks past
   --  private types.

   function Has_Static_Scalar_Subtype (T : Entity_Id) return Boolean is
      Under_T  : constant Entity_Id := Underlying_Type (T);
      Base_T   : constant Entity_Id := Base_Type (Under_T);
      Anc_Subt : Entity_Id;

   begin
      Anc_Subt := Ancestor_Subtype (Under_T);

      if Anc_Subt = Empty then
         Anc_Subt := Base_T;
      end if;

      if not Has_Scalar_Type (Under_T) then
         return False;

      elsif Base_T = Under_T then
         return True;

      else
         return     Has_Static_Scalar_Subtype (Anc_Subt)
           and then Is_Static_Expression (Type_Low_Bound (Under_T))
           and then Is_Static_Expression (Type_High_Bound (Under_T));
      end if;
   end Has_Static_Scalar_Subtype;

   function Retysp (T : Entity_Id) return Entity_Id is
      Typ : Entity_Id := T;

   begin
      --  If T has not been marked yet, return it

      if not Entity_Marked (T) then
         return T;
      end if;

      --  If T is not in SPARK, go through the Partial_View chain to find its
      --  first view in SPARK if any.

      if not Entity_In_SPARK (T) then
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

      elsif Full_View_Not_In_SPARK (T) then
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

   function Retysp_Kind (T : Entity_Id) return Entity_Kind is
      Typ : Entity_Id := T;
   begin
      while Is_Private_Type (Typ) loop
         Typ := Underlying_Type (Typ);
      end loop;
      return Ekind (Typ);
   end Retysp_Kind;

   ------------------------------------
   -- Aggregate_Is_Fully_Initialized --
   ------------------------------------

   function Aggregate_Is_Fully_Initialized (N : Node_Id) return Boolean is

      function Matching_Component_Association
        (Component   : Entity_Id;
         Association : Node_Id) return Boolean;
      --  Return whether Association matches Component

      procedure Skip_Ancestor_And_Generated_Components
        (Component : in out Entity_Id);
      --  If Component is either a component belonging to an ancestor
      --  or a compiler generated component, skip it and all similar
      --  following components.

      ------------------------------------
      -- Matching_Component_Association --
      ------------------------------------

      function Matching_Component_Association
        (Component   : Entity_Id;
         Association : Node_Id) return Boolean
      is
         CL : constant List_Id := Choices (Association);
      begin
         pragma Assert (List_Length (CL) = 1);
         declare
            Assoc : constant Node_Id := Entity (First (CL));
         begin
            --  ??? In some cases, it is necessary to go through the
            --  Root_Record_Component to compare the component from the
            --  aggregate type (Component) and the component from the aggregate
            --  (Assoc). We don't understand why this is needed.

            return Component = Assoc
              or else
                Original_Record_Component (Component) =
              Original_Record_Component (Assoc)
              or else
                Root_Record_Component (Component) =
              Root_Record_Component (Assoc);
         end;
      end Matching_Component_Association;

      --------------------------------------------
      -- Skip_Ancestor_And_Generated_Components --
      --------------------------------------------

      procedure Skip_Ancestor_And_Generated_Components
        (Component : in out Entity_Id)
      is
         function Is_Ancestor_Component (Component : Entity_Id) return Boolean;
         --  Returns True if the component in question comes from the
         --  ancestor.

         ---------------------------
         -- Is_Ancestor_Component --
         ---------------------------

         function Is_Ancestor_Component (Component : Entity_Id) return Boolean
         is
            Ancestor_Typ  : Entity_Id;
            Ancestor_Comp : Entity_Id;
         begin
            if Nkind (N) /= N_Extension_Aggregate or else
              No (Ancestor_Part (N))
            then
               return False;
            end if;

            Ancestor_Typ  := Retysp (Etype (Ancestor_Part (N)));
            Ancestor_Comp := First_Component_Or_Discriminant (Ancestor_Typ);

            while Present (Ancestor_Comp) loop
               if Component = Ancestor_Comp
                 or else Original_Record_Component (Component) =
                           Original_Record_Component (Ancestor_Comp)
                 or else Root_Record_Component (Component) =
                           Root_Record_Component (Ancestor_Comp)
               then
                  return True;
               end if;

               Ancestor_Comp := Next_Component_Or_Discriminant (Ancestor_Comp);
            end loop;

            return False;
         end Is_Ancestor_Component;

      begin
         while Present (Component)
           and then (not Comes_From_Source (Component)
                       or else Is_Ancestor_Component (Component))
         loop
            Component := Next_Component_Or_Discriminant (Component);
         end loop;
      end Skip_Ancestor_And_Generated_Components;

      Typ         : constant Entity_Id := Retysp (Etype (N));
      Assocs      : List_Id;
      Component   : Entity_Id;
      Association : Node_Id;
      Not_Init    : constant Boolean :=
        Default_Initialization (Typ) /= Full_Default_Initialization;

   --  Start of processing for Aggregate_Is_Fully_Initialized

   begin
      if Is_Record_Type (Typ) or else Is_Private_Type (Typ) then
         pragma Assert (Is_Empty_List (Expressions (N)));

         Assocs      := Component_Associations (N);
         Component   := First_Component_Or_Discriminant (Typ);
         Association := First (Assocs);

         Skip_Ancestor_And_Generated_Components (Component);

         while Present (Component) loop
            if Present (Association)
              and then Matching_Component_Association (Component, Association)
            then
               if Box_Present (Association) and then Not_Init then
                  return False;
               end if;
               Next (Association);
            else
               return False;
            end if;

            Component := Next_Component_Or_Discriminant (Component);
            Skip_Ancestor_And_Generated_Components (Component);
         end loop;

      else
         pragma Assert (Is_Array_Type (Typ) or else Is_String_Type (Typ));

         Assocs := Component_Associations (N);

         if Present (Assocs) then
            Association := First (Assocs);

            while Present (Association) loop
               if Box_Present (Association) and then Not_Init then
                  return False;
               end if;
               Next (Association);
            end loop;
         end if;
      end if;

      return True;
   end Aggregate_Is_Fully_Initialized;

   ------------------------
   -- Analysis_Requested --
   ------------------------

   function Analysis_Requested (E : Entity_Id) return Boolean is
   begin
      return Is_In_Analyzed_Files (E)

       --  Either the analysis is requested for the complete unit, or if it is
       --  requested for a specific subprogram/task, check whether it is E.

        and then (Gnat2Why_Args.Limit_Subp = Null_Unbounded_String
                    or else
                  Is_Requested_Subprogram_Or_Task (E))

        --  Ignore inlined subprograms that are referenced. Unreferenced
        --  subprograms are analyzed anyway, as they are likely to correspond
        --  to an intermediate stage of development. Also always analyze the
        --  subprogram if analysis was specifically requested for it.

        and then (not Is_Local_Subprogram_Always_Inlined (E)
                    or else
                  not Referenced (E)
                    or else
                  Is_Requested_Subprogram_Or_Task (E));
   end Analysis_Requested;

   ------------
   -- Append --
   ------------

   procedure Append
     (To    : in out Node_Lists.List;
      Elmts : Node_Lists.List) is
   begin
      for E of Elmts loop
         To.Append (E);
      end loop;
   end Append;

   procedure Append
     (To    : in out Why_Node_Lists.List;
      Elmts : Why_Node_Lists.List) is
   begin
      for E of Elmts loop
         To.Append (E);
      end loop;
   end Append;

   --------------------
   -- Body_File_Name --
   --------------------

   function Body_File_Name (N : Node_Id) return String is
      CU     : Node_Id := Enclosing_Lib_Unit_Node (N);
      Switch : constant Boolean :=
        Nkind (Unit (CU)) not in N_Package_Body | N_Subprogram_Body;

   begin
      if Switch and then Present (Library_Unit (CU)) then
         CU := Library_Unit (CU);
      end if;

      return File_Name (Sloc (CU));
   end Body_File_Name;

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
        and then not Is_Constrained (To_R)
        and then (not Is_Tagged_Type (To_R) or else Is_Ancestor (To_R, From_R))
        and then not Has_Predicates (To_R)
      then
         return False;

      --  Otherwise a check may be needed

      else
         return True;
      end if;
   end Check_Needed_On_Conversion;

   -----------------------------------
   -- Component_Is_Visible_In_SPARK --
   -----------------------------------

   function Component_Is_Visible_In_SPARK (E : Entity_Id) return Boolean is
   begin
      if Ekind (E) = E_Discriminant then
         return True;
      else
         declare
            Orig_Comp : constant Entity_Id := Original_Record_Component (E);
            Orig_Rec  : constant Entity_Id := Scope (Orig_Comp);
            Pview_Rec : constant Entity_Id :=
              (if Present (Full_View (Orig_Rec))
               then Full_View (Orig_Rec)
               else Orig_Rec);
         begin
            return Entity_In_SPARK (Pview_Rec);
         end;
      end if;
   end Component_Is_Visible_In_SPARK;

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
      Field : Entity_Id;
      Count : Natural := 0;

   begin
      if Is_Record_Type (E) or else Is_Protected_Type (E) then
         Field := First_Component (E);
         while Present (Field) loop
            if not Is_Tag (Field)
              and then Component_Is_Visible_In_SPARK (Field)
            then
               Count := Count + 1;
            end if;
            Next_Component (Field);
         end loop;
      end if;

      --  Add one field for private types whose components are not visible.

      if Is_Private_Type (E) or else Is_Task_Type (E) then
         Count := Count + 1;
      end if;

      --  Add one field for tagged types to represent the unknown extension
      --  components. The field for the tag itself is stored directly in the
      --  Why3 record.

      if Is_Tagged_Type (E) then
         Count := Count + 1;

         --  Add one field for record types with a private ancestor, whose
         --  components are not visible.

         if Has_Private_Ancestor_Or_Root (E) then
            Count := Count + 1;
         end if;
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

      if not Is_Constrained (E) and then Has_Defaulted_Discriminants (E) then
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

      function Get_Default_Init_Cond_Pragma (Typ : Entity_Id) return Node_Id
        with Pre => Has_Default_Init_Cond (Typ) or else
                    Has_Inherited_Default_Init_Cond (Typ);
      --  Returns the unanalyzed pragma Default_Initial_Condition applying to a
      --  type.

      procedure Process_Component (Rec_Prot_Comp : Entity_Id);
      --  Process component Rec_Prot_Comp of a record or protected type

      ----------------------------------
      -- Get_Default_Init_Cond_Pragma --
      ----------------------------------

      function Get_Default_Init_Cond_Pragma (Typ : Entity_Id) return Node_Id is
         Par : Entity_Id := Typ;
      begin
         while Has_Default_Init_Cond (Par)
           or else Has_Inherited_Default_Init_Cond (Par)
         loop
            if Has_Default_Init_Cond (Par) then
               return Get_Pragma (Typ, Pragma_Default_Initial_Condition);
            elsif Is_Private_Type (Par) and then Etype (Par) = Par then
               Par := Etype (Full_View (Par));
            else
               Par := Etype (Par);
            end if;
         end loop;

         --  We should not reach here

         raise Program_Error;
      end Get_Default_Init_Cond_Pragma;

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
      --  Has_Default_Init_Cond and Has_Inherited_Default_Init_Cond on
      --  the base type instead. However, we want to skip Itypes while
      --  doing so.

      B_Type := Typ;
      if Ekind (B_Type) in Subtype_Kind then
         while (Ekind (B_Type) in Subtype_Kind
                  or else Is_Itype (B_Type))

           --  Stop if we find either of the attributes
           and then not (Has_Default_Init_Cond (B_Type)
                           or else Has_Inherited_Default_Init_Cond (B_Type))

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
        and then (Has_Default_Init_Cond (B_Type)
                    or else Has_Inherited_Default_Init_Cond (B_Type))
      then
         declare
            Prag : constant Node_Id := Get_Default_Init_Cond_Pragma (B_Type);
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
         if Present (Default_Aspect_Component_Value (Base_Type (Typ))) then
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

   ----------------
   -- Entry_Body --
   ----------------

   function Entry_Body (E : Entity_Id) return Node_Id
   is
      Ptr : Node_Id := Entry_Body_Entity (E);
   begin
      if Present (Ptr) then
         Ptr := Parent (Ptr);
      end if;
      return Ptr;
   end Entry_Body;

   -----------------------
   -- Entry_Body_Entity --
   -----------------------

   function Entry_Body_Entity (E : Entity_Id) return Entity_Id
   is
      Ptr : constant Node_Id := Parent (E);
   begin
      pragma Assert (Nkind (Ptr) = N_Entry_Declaration);
      return Corresponding_Body (Ptr);
   end Entry_Body_Entity;

   --------------------
   -- Find_Contracts --
   --------------------

   function Find_Contracts
     (E         : Entity_Id;
      Name      : Name_Id;
      Classwide : Boolean := False;
      Inherited : Boolean := False) return Node_Lists.List
   is
      C         : Node_Id := Contract (E);
      P         : Node_Id;
      Contracts : Node_Lists.List := Node_Lists.Empty_List;

   begin
      --  If Inherited is True, look for an inherited contract, starting from
      --  the closest overridden subprogram.

      --  ??? Does not work for multiple inheritance through interfaces

      if Inherited then
         declare
            Inherit_Subp : constant Subprogram_List :=
              Inherited_Subprograms (E);
         begin
            for J in Inherit_Subp'Range loop
               Contracts :=
                 Find_Contracts (Inherit_Subp (J), Name, Classwide => True);

               if not Contracts.Is_Empty then
                  return Contracts;
               end if;
            end loop;
         end;

         return Contracts;
      end if;

      case Name is
         when Name_Precondition      |
              Name_Postcondition     |
              Name_Refined_Post      |
              Name_Contract_Cases    |
              Name_Initial_Condition =>

            if Name = Name_Refined_Post then
               if Ekind (E) in Subprogram_Kind
                 and then Present (Subprogram_Body (E))
               then
                  C := Contract (Defining_Entity (Specification
                                                    (Subprogram_Body (E))));
               elsif Ekind (E) = E_Entry
                 and then Present (Entry_Body (E))
               then
                  C := Contract (Entry_Body_Entity (E));
               else
                  C := Empty;
               end if;
            end if;

            if Present (C) then
               P := (case Name is
                        when Name_Precondition  |
                             Name_Postcondition |
                             Name_Refined_Post  => Pre_Post_Conditions (C),
                        when Name_Initial_Condition => Classifications (C),
                        when others => Contract_Test_Cases (C));

               while Present (P) loop
                  if Chars (Pragma_Identifier (P)) = Name
                    and then Classwide = Class_Present (P)
                  then
                     Contracts.Append
                       (Expression (First (Pragma_Argument_Associations (P))));
                  end if;

                  P := Next_Pragma (P);
               end loop;

            end if;

            return Contracts;

         when Name_Global | Name_Depends =>
            raise Why.Not_Implemented;

         when others =>
            raise Program_Error;
      end case;
   end Find_Contracts;

   ---------------
   -- Full_Name --
   ---------------

   function Full_Name (E : Entity_Id) return String is
   begin
      --  In a few special cases, return a predefined name. These cases should
      --  match those for which Full_Name_Is_Not_Unique_Name returns True.

      if Full_Name_Is_Not_Unique_Name (E) then
         if Is_Standard_Boolean_Type (E) then
            return "bool";
         elsif E = Universal_Fixed then
            return "real";
         else
            raise Program_Error;
         end if;

      --  In the general case, return the same name as Unique_Name

      else
         return Unique_Name (E);
      end if;
   end Full_Name;

   ----------------------------------
   -- Full_Name_Is_Not_Unique_Name --
   ----------------------------------

   function Full_Name_Is_Not_Unique_Name (E : Entity_Id) return Boolean is
     (Is_Standard_Boolean_Type (E) or else E = Universal_Fixed);

   -----------------------
   -- Get_Called_Entity --
   -----------------------

   function Get_Called_Entity (N : Node_Id) return Entity_Id is
      Nam : constant Node_Id := Name (N);
   begin
      return Entity (if Nkind (Nam) = N_Selected_Component
                     then Selector_Name (Nam)
                     else Nam);
   end Get_Called_Entity;

   ------------------------
   -- Get_Execution_Kind --
   ------------------------

   function Get_Execution_Kind
     (E        : Entity_Id;
      After_GG : Boolean := True) return Execution_Kind_T
   is
      function Has_No_Output return Boolean;
      --  Return True if procedure E has no output (parameter or global).
      --  Otherwise, or if we don't know for sure, we return False. If
      --  After_GG is False, then we will not query generated globals.

      -------------------
      -- Has_No_Output --
      -------------------

      function Has_No_Output return Boolean is
         Params : constant List_Id :=
           Parameter_Specifications (Subprogram_Specification (E));
         Param  : Node_Id;

         Read_Ids    : Flow_Types.Flow_Id_Sets.Set;
         Write_Ids   : Flow_Types.Flow_Id_Sets.Set;
         Write_Names : Name_Sets.Set;

      begin
         --  Consider output parameters

         Param := First (Params);
         while Present (Param) loop
            case Formal_Kind'(Ekind (Defining_Identifier (Param))) is
            when E_Out_Parameter | E_In_Out_Parameter =>
               return False;
            when E_In_Parameter =>
               null;
            end case;
            Next (Param);
         end loop;

         --  Consider output globals if they can be relied upon, either because
         --  this is after the generation of globals, or because the user has
         --  supplied them.

         if After_GG or else Has_User_Supplied_Globals (E) then
            Flow_Utility.Get_Proof_Globals (Subprogram => E,
                                            Classwide  => True,
                                            Reads      => Read_Ids,
                                            Writes     => Write_Ids);
            Write_Names := Flow_Types.To_Name_Set (Write_Ids);

            return Write_Names.Is_Empty;

         --  Otherwise we don't know, return False to be on the safe side

         else
            return False;
         end if;
      end Has_No_Output;

   begin
      if Has_No_Output then
         return Abnormal_Termination;
      else
         return Infinite_Loop;
      end if;
   end Get_Execution_Kind;

   -----------------------------------
   -- Get_Expr_From_Check_Only_Proc --
   -----------------------------------

   function Get_Expr_From_Check_Only_Proc (E : Entity_Id) return Node_Id is
      Body_N : constant Node_Id := Subprogram_Body (E);
      Stmt   : Node_Id;
      Arg    : Node_Id;

   begin
      --  If there is no associated body, return Empty.

      if No (Body_N) then
         return Empty;
      end if;

      Stmt := First (Statements (Handled_Statement_Sequence (Body_N)));

      while Present (Stmt) loop

         --  Return the second argument of the first pragma Check in the
         --  statement list if any.

         if Nkind (Stmt) = N_Pragma
           and then Get_Pragma_Id (Pragma_Name (Stmt)) = Pragma_Check
         then
            pragma Assert (Present (Pragma_Argument_Associations (Stmt)));
            Arg := First (Pragma_Argument_Associations (Stmt));
            pragma Assert (Present (Arg));
            Arg := Next (Arg);
            pragma Assert (Present (Arg));
            return (Get_Pragma_Arg (Arg));
         end if;

         Next (Stmt);
      end loop;

      --  Otherwise return Empty

      return Empty;
   end Get_Expr_From_Check_Only_Proc;

   ------------------------------------
   -- Get_Expr_From_Return_Only_Func --
   ------------------------------------

   function Get_Expr_From_Return_Only_Func (E : Entity_Id) return Node_Id is
      Body_N : constant Node_Id := Subprogram_Body (E);
      Stmt   : Node_Id;

   begin
      --  If there is no associated body, return Empty.

      if No (Body_N) then
         return Empty;
      end if;

      Stmt := First (Statements (Handled_Statement_Sequence (Body_N)));

      while Present (Stmt) loop

         --  Return the argument of the first return statement in the statement
         --  list if any.

         if Nkind (Stmt) = N_Simple_Return_Statement then
            return Expression (Stmt);
         end if;

         Next (Stmt);
      end loop;

      --  Otherwise return Empty

      return Empty;
   end Get_Expr_From_Return_Only_Func;

   -----------------------------
   -- Get_Expression_Function --
   -----------------------------

   function Get_Expression_Function (E : Entity_Id) return Node_Id is
      Decl_N : constant Node_Id := Parent (Subprogram_Specification (E));
      Body_N : constant Node_Id := Subprogram_Body (E);
      Orig_N : Node_Id;

   begin
      --  Get the original node either from the declaration for E, or from the
      --  subprogram body for E, which may be different if E is attached to a
      --  subprogram declaration.

      if Present (Original_Node (Decl_N))
        and then Original_Node (Decl_N) /= Decl_N
      then
         Orig_N := Original_Node (Decl_N);
      else
         Orig_N := Original_Node (Body_N);
      end if;

      if Nkind (Orig_N) = N_Expression_Function then
         return Orig_N;
      else
         return Empty;
      end if;
   end Get_Expression_Function;

   ---------------------------------------------
   -- Get_Flat_Statement_And_Declaration_List --
   ---------------------------------------------

   function Get_Flat_Statement_And_Declaration_List
     (Stmts : List_Id) return Node_Lists.List
   is
      Cur_Stmt   : Node_Id := Nlists.First (Stmts);
      Flat_Stmts : Node_Lists.List;

   begin
      while Present (Cur_Stmt) loop
         case Nkind (Cur_Stmt) is
            when N_Block_Statement =>
               if Present (Declarations (Cur_Stmt)) then
                  Append (Flat_Stmts,
                          Get_Flat_Statement_And_Declaration_List
                            (Declarations (Cur_Stmt)));
               end if;

               Append (Flat_Stmts,
                       Get_Flat_Statement_And_Declaration_List
                         (Statements (Handled_Statement_Sequence (Cur_Stmt))));

            when others =>
               Flat_Stmts.Append (Cur_Stmt);
         end case;

         Nlists.Next (Cur_Stmt);
      end loop;

      return Flat_Stmts;
   end Get_Flat_Statement_And_Declaration_List;

   ---------------------------------
   -- Get_Formal_Type_From_Actual --
   ---------------------------------

   function Get_Formal_From_Actual (Actual : Node_Id) return Entity_Id is
      Formal : Entity_Id := Empty;

      procedure Check_Call_Arg (Some_Formal, Some_Actual : Node_Id);
      --  If Some_Actual is the desired actual parameter, set Formal_Type to
      --  the type of the corresponding formal parameter.

      --------------------
      -- Check_Call_Arg --
      --------------------

      procedure Check_Call_Arg (Some_Formal, Some_Actual : Node_Id) is
      begin
         if Some_Actual = Actual then
            Formal := Some_Formal;
         end if;
      end Check_Call_Arg;

      procedure Find_Expr_In_Call_Args is new
        Iterate_Call_Arguments (Check_Call_Arg);

      Par : constant Node_Id :=
        (if Nkind (Parent (Actual)) = N_Unchecked_Type_Conversion
           and then Comes_From_Source (Parent (Actual))
         then Original_Node (Parent (Actual)) else Parent (Actual));
      --  N_Unchecked_Type_Conversion coming from source are handled using
      --  their original node.

   begin
      if Nkind (Par) = N_Parameter_Association then
         Find_Expr_In_Call_Args (Parent (Par));
      else
         Find_Expr_In_Call_Args (Par);
      end if;

      pragma Assert (Present (Formal));

      return Formal;
   end Get_Formal_From_Actual;

   ------------------------------------
   -- Get_Full_Type_Without_Checking --
   ------------------------------------

   function Get_Full_Type_Without_Checking (N : Node_Id) return Entity_Id is
      T : constant Entity_Id := Etype (N);
   begin
      if Nkind (N) in N_Entity and then Ekind (N) = E_Abstract_State then
         return T;
      else
         pragma Assert (Nkind (T) in N_Entity);
         pragma Assert (Is_Type (T));
         if Present (Full_View (T)) then
            return Full_View (T);
         else
            return T;
         end if;
      end if;
   end Get_Full_Type_Without_Checking;

   ----------------------
   -- Get_Global_Items --
   ----------------------

   procedure Get_Global_Items
     (P      :     Node_Id;
      Reads  : out Node_Sets.Set;
      Writes : out Node_Sets.Set)
   is
      pragma Assert (List_Length (Pragma_Argument_Associations (P)) = 1);

      PAA : constant Node_Id := First (Pragma_Argument_Associations (P));
      pragma Assert (Nkind (PAA) = N_Pragma_Argument_Association);

      Row      : Node_Id;
      The_Mode : Name_Id;
      RHS      : Node_Id;

      procedure Process (The_Mode   : Name_Id;
                         The_Global : Entity_Id);
      --  Add the given global to the reads or writes list,
      --  depending on the mode.

      procedure Process (The_Mode   : Name_Id;
                         The_Global : Entity_Id) is
      begin
         case The_Mode is
            when Name_Input =>
               Reads.Insert (The_Global);
            when Name_In_Out =>
               Reads.Insert (The_Global);
               Writes.Insert (The_Global);
            when Name_Output =>
               Writes.Insert (The_Global);
            when others =>
               raise Program_Error;
         end case;
      end Process;

   --  Start of processing for Get_Global_Items

   begin
      Reads  := Node_Sets.Empty_Set;
      Writes := Node_Sets.Empty_Set;

      if Nkind (Expression (PAA)) = N_Null then
         --  global => null
         --  No globals, nothing to do.
         return;

      elsif Nkind (Expression (PAA)) in
        N_Identifier | N_Expanded_Name
      then
         --  global => foo
         --  A single input
         Process (Name_Input, Entity (Expression (PAA)));

      elsif Nkind (Expression (PAA)) = N_Aggregate and then
        Expressions (Expression (PAA)) /= No_List
      then
         --  global => (foo, bar)
         --  Inputs
         RHS := First (Expressions (Expression (PAA)));
         while Present (RHS) loop
            case Nkind (RHS) is
               when N_Identifier | N_Expanded_Name =>
                  Process (Name_Input, Entity (RHS));
               when others =>
                  raise Why.Unexpected_Node;
            end case;
            RHS := Next (RHS);
         end loop;

      elsif Nkind (Expression (PAA)) = N_Aggregate and then
        Component_Associations (Expression (PAA)) /= No_List
      then
         --  global => (mode => foo,
         --             mode => (bar, baz))
         --  A mixture of things.

         declare
            CA : constant List_Id :=
              Component_Associations (Expression (PAA));
         begin
            Row := First (CA);
            while Present (Row) loop
               pragma Assert (List_Length (Choices (Row)) = 1);
               The_Mode := Chars (First (Choices (Row)));

               RHS := Expression (Row);
               case Nkind (RHS) is
                  when N_Aggregate =>
                     RHS := First (Expressions (RHS));
                     while Present (RHS) loop
                        Process (The_Mode, Entity (RHS));
                        RHS := Next (RHS);
                     end loop;
                  when N_Identifier | N_Expanded_Name =>
                     Process (The_Mode, Entity (RHS));
                  when N_Null =>
                     null;
                  when others =>
                     Print_Node_Subtree (RHS);
                     raise Why.Unexpected_Node;
               end case;

               Row := Next (Row);
            end loop;
         end;

      else
         raise Why.Unexpected_Node;
      end if;
   end Get_Global_Items;

   ---------------
   -- Get_Range --
   ---------------

   function Get_Range (N : Node_Id) return Node_Id is
   begin
      case Nkind (N) is
         when N_Range                           |
              N_Real_Range_Specification        |
              N_Signed_Integer_Type_Definition  |
              N_Modular_Type_Definition         |
              N_Floating_Point_Definition       |
              N_Ordinary_Fixed_Point_Definition |
              N_Decimal_Fixed_Point_Definition  =>
            return N;

         when N_Subtype_Indication =>
            return Range_Expression (Constraint (N));

         when N_Identifier | N_Expanded_Name =>
            return Get_Range (Entity (N));

         when N_Defining_Identifier =>
            case Ekind (N) is
               when Scalar_Kind =>
                  return Get_Range (Scalar_Range (N));

               when Object_Kind =>
                  return Get_Range (Scalar_Range (Etype (N)));

               when others =>
                  raise Program_Error;
            end case;

         when others =>
            raise Program_Error;
      end case;
   end Get_Range;

   --------------------------------------
   -- Get_Specific_Type_From_Classwide --
   --------------------------------------

   function Get_Specific_Type_From_Classwide (E : Entity_Id) return Entity_Id
   is
      S : constant Entity_Id := Etype (E);
   begin
      if Is_Full_View (S) then
         return Partial_View (S);
      else
         return S;
      end if;
   end Get_Specific_Type_From_Classwide;

   ----------------------------------------
   -- Get_Statement_And_Declaration_List --
   ----------------------------------------

   function Get_Statement_And_Declaration_List
     (Stmts : List_Id) return Node_Lists.List
   is
      Cur_Stmt   : Node_Id := Nlists.First (Stmts);
      New_Stmts : Node_Lists.List;

   begin
      while Present (Cur_Stmt) loop
         New_Stmts.Append (Cur_Stmt);
         Nlists.Next (Cur_Stmt);
      end loop;

      return New_Stmts;
   end Get_Statement_And_Declaration_List;

   -------------------
   -- Has_Contracts --
   -------------------

   function Has_Contracts
     (E         : Entity_Id;
      Name      : Name_Id;
      Classwide : Boolean := False;
      Inherited : Boolean := False) return Boolean
   is
      Contracts : Node_Lists.List;

   begin
      if Classwide or Inherited then
         if Classwide then
            Contracts := Find_Contracts (E, Name, Classwide => True);
         end if;

         if Contracts.Is_Empty and Inherited then
            Contracts := Find_Contracts (E, Name, Inherited => True);
         end if;

      else
         Contracts := Find_Contracts (E, Name);
      end if;

      return not Contracts.Is_Empty;
   end Has_Contracts;

   ----------------------------
   -- Has_Extensions_Visible --
   ----------------------------

   function Has_Extensions_Visible (E : Entity_Id) return Boolean is
     (Present (Get_Pragma (E, Pragma_Extensions_Visible)));

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

   -----------------------------------
   -- Has_Static_Discrete_Predicate --
   -----------------------------------

   function Has_Static_Discrete_Predicate (E : Entity_Id) return Boolean is
     (Is_Discrete_Type (E)
       and then Has_Predicates (E)
       and then Present (Static_Discrete_Predicate (E)));

   -------------------------------
   -- Has_User_Supplied_Globals --
   -------------------------------

   function Has_User_Supplied_Globals (E : Entity_Id) return Boolean is
     (Present (Get_Pragma (E, Pragma_Global))
       or else Present (Get_Pragma (E, Pragma_Depends)));

   ------------------
   -- Has_Volatile --
   ------------------

   function Has_Volatile (E : Entity_Id) return Boolean is
     (case Ekind (E) is
         when E_Abstract_State =>
            Is_External_State (E),
         when Object_Kind =>
            Is_Effectively_Volatile (E),
         when others =>
            raise Program_Error);

   -------------------------
   -- Has_Volatile_Flavor --
   -------------------------

   function Has_Volatile_Flavor
     (E : Entity_Id;
      A : Pragma_Id) return Boolean
   is
   begin
      case Ekind (E) is
         when E_Abstract_State | E_Variable =>
            case A is
               when Pragma_Async_Readers =>
                  return Async_Readers_Enabled (E);
               when Pragma_Async_Writers =>
                  return Async_Writers_Enabled (E);
               when Pragma_Effective_Reads =>
                  return Effective_Reads_Enabled (E);
               when Pragma_Effective_Writes =>
                  return Effective_Writes_Enabled (E);
               when others =>
                  raise Program_Error;
            end case;

         --  Why restrict the flavors of volatility for IN and OUT
         --  parameters???

         when E_In_Parameter =>
            case A is
               when Pragma_Async_Writers =>
                  return True;
               when Pragma_Async_Readers
                  | Pragma_Effective_Reads
                  | Pragma_Effective_Writes =>
                  return False;
               when others =>
                  raise Program_Error;
            end case;

         when E_Out_Parameter =>
            case A is
               when Pragma_Async_Writers
                  | Pragma_Effective_Reads =>
                  return False;
               when Pragma_Async_Readers
                  | Pragma_Effective_Writes =>
                  return True;
               when others =>
                  raise Program_Error;
            end case;

         when E_In_Out_Parameter =>
            return True;

         when others =>
            raise Program_Error;
      end case;
   end Has_Volatile_Flavor;

   -------------------------------------
   -- Has_Only_Nonblocking_Statements --
   -------------------------------------

   function Has_Only_Nonblocking_Statements (N : Node_Id) return Boolean is

      Potentially_Blocking_Statement_Found : Boolean := False;
      --  Flag used as an output for the AST traversal procedure

      function Proc (N : Node_Id) return Traverse_Result;
      --  Process a node to check if it is a potentially blocking statement

      procedure Traverse is new Traverse_Proc (Proc);
      --  Traverse a tree to check if it includes blocking statements

      function Is_Predefined_Potentially_Blocking
        (E : Entity_Id)
         return Boolean;
      --  Check if entity E is a predefined potentially blocking subprogram

      ----------------------------------------
      -- Is_Predefined_Potentially_Blocking --
      ----------------------------------------

      function Is_Predefined_Potentially_Blocking
        (E : Entity_Id)
         return Boolean
      is
         --  Detect:
         --    Ada.Task_Identification.Abort_Task
         --    Ada.Dispatching.Yield
         --    Ada.Synchronous_Task_Control.Suspend_Until_True
         --    Ada.Synchronous_Task_Control.EDF.
         --        Suspend_Until_True_And_Set_Deadline
         --    Ada.Synchronous_Barriers.Wait_For_Release
         --    System.RPC.*
         --
         --  and file-manipulating subprograms:
         --    Ada.Directories.*
         --    Ada.Text_IO.*
         --    Ada.Wide_Text_IO.*
         --    Ada.Wide_Wide_Text_IO.*
         --    Ada.Direct_IO.*
         --    Ada.Sequential_IO.*
         --    Ada.Streams.*
         --
         --  with notable exception of
         --    Ada.Storage_IO (input-output to memory buffer).

         --  It is more natural to detect these subprograms by first collecting
         --  the scope hierarchy and then analysing it starting from the
         --  outermost scope.
         --
         --  Note: to detect any of the predefined potentially blocking
         --  subprograms we only need up to 5 outermost scopes, like:
         --    (0) Standard.
         --    (1)  Ada.
         --    (2)   Text_IO.
         --    (3)    Editing.
         --    (4)     Decimal_Output
         --  and for System.RPC.* we need only the 3 outermost scopes, i.e.
         --    (0) Standard.
         --    (1)  System.
         --    (2)   RPC.
         --  Thus we avoid the use of much heavier Ada.Container.Vector/List,
         --  and use a circullar buffer instead.

         Max_Predefined_Potentially_Blocking_Nesting : constant := 5;
         --  Maximal nesting of predefined potentially blocking subprograms

         type Scope_Index is mod Max_Predefined_Potentially_Blocking_Nesting;
         --  Modular type for indexing the circullar buffer

         Scopes : array (Scope_Index) of Entity_Id;
         --  Circullar buffer with scopes of a call

         Scope_Id : Scope_Index := Scope_Index'Last;
         --  Indexing variable

         function Scope_Name (Nth : Scope_Index) return Name_Id with
         Pure_Function;
         --  Return name of the Nth scope for the analyzed entity.
         --  For 0 the result is always Standard,
         --  For 1 the result is Ada/Interfaces/System or user-defined,
         --  Etc.
         --
         --  Aspect Pure_Function is ment to improve performance when using
         --  this function as an array.

         ----------------
         -- Scope_Name --
         ----------------

         function Scope_Name (Nth : Scope_Index) return Name_Id is
            (Chars (Scopes (Scope_Id + Nth)));

      begin
         --  Start from the called subprogram
         Scopes (Scope_Id) := E;

         --  Collect scopes up to the outermost one, i.e. Standard
         while Scopes (Scope_Id) /= Standard_Standard loop
            declare
               Parent_Scope : Entity_Id := Scope (Scopes (Scope_Id));
            begin
               --  If the parent scope is an instance of a generic package
               --  then analyze the generic and not its instance.
               if Ekind (Parent_Scope) = E_Package
                 and then Is_Generic_Instance (Parent_Scope)
               then
                  Parent_Scope :=
                    Entity (Name (
                            Get_Package_Instantiation_Node (Parent_Scope)));
               end if;

               Scope_Id := Scope_Id - 1;
               Scopes (Scope_Id) := Parent_Scope;
            end;
         end loop;
         --  Now we have something like:
         --  Scopes (Scope_Id)     -> Standard
         --  Scopes (Scope_Id + 1) -> Ada/Interfaces/System/...
         --  Scopes (Scope_Id + 2) -> Synchronous_Task_Control/...
         --  Scopes (Scope_Id + 3) -> EDF/Suspend_Until_True/...
         --  Scopes (Scope_Id + 4) -> Suspend_Until_True_And_Set_Deadline/...

         --  Dive into the scope hierarchy and look for names of predefined
         --  blocking subprograms.
         case Scope_Name (1) is
            when Name_Ada =>
               --  Further checks needed
               null;

            when Name_Interfaces =>
               --  All subprograms in package Interfaces are nonblocking
               return False;

            when Name_System =>
               --  Only subprograms in System.RPC are blocking
               return Scope_Name (2) = Name_Rpc;

            when others =>
               --  It is a user-defined subprogram and the call itself is
               --  nonblocking. If the target subprogram is potentially
               --  blocking, then it will be detected by call graph traversal.
               return False;
         end case;

         --  All subprograms in the child packages of Ada are blocking
         if Scope_Name (2) in Name_Directories   |
                              Name_Direct_IO     |
                              Name_Sequential_IO |
                              Name_Streams
         then
            --  Ada.Directories.Hierarchical_File_Names seems nonblocking. We
            --  conciously ignore it, since it is not yet implemented in GNAT
            --  and extremely unlikely to be needed in nonblocking contexts.
            return True;

         --  Child packages of Ada.[Wide_[Wide_]]Text_IO are identical
         elsif Scope_Name (2) in Name_Text_IO         |
                                 Name_Wide_Text_IO    |
                                 Name_Wide_Wide_Text_IO
         then
            --  Operations on bounded/unbounded strings either print or read
            --  them and thus are potentially blocking.
            if Scope_Name (3) in Name_Bounded_IO | Name_Unbounded_IO
            then
               return True;

            --  These generics have both blocking and nonblocking Put/Get
            elsif Scope_Name (3) in Name_Complex_IO | Text_IO_Package_Name
            then
               --  The name of the subproram (i.e. Put or Get) makes
               --  no difference (and it troublesome to know because of
               --  overriding). Blocking/Nonblocking status is determined
               --  by the name of the first formal parameter.
               --  * "File" means input/output to a specific file
               --  * "Item" means input/output to a default file
               --  * anything else means input/output to a string buffer
               return Chars (First_Formal (E)) in Name_File | Name_Item;

            --  These packages operate only on internal data structers and thus
            --  are nonblocking.
            elsif Scope_Name (3) in Name_C_Streams          |
                                    Name_Text_Streams       |
                                    Name_Reset_Standard_Files
            then
               return False;

            --  Ada.Text_IO.Editing is nonblocking, except for Decimal_IO
            elsif Scope_Name (3) = Name_Editing
            then
               if Scope_Name (4) = Name_Decimal_IO then
                  --  The only blocking subprograms are:
                  --    procedure Put (File : Ada.Text_IO.File_Type; ...)
                  --    procedure Put (Item : Num; ...)
                  --  and they are also detected by the name of the first
                  --  formal parameter.
                  return Ekind (E) = E_Procedure and then
                    Chars (First_Formal (E)) in Name_File | Name_Item;
               else
                  return False;
               end if;
            else
               --  Assume that all subprograms directly within Ada.Text_IO
               --  are potentially blocking. This is true for most of them,
               --  e.g. for Create/Open/Close/Delete, but in GNAT there few
               --  exceptions, e.g. Mode/Name/Form/Is_Open. However, they can
               --  be blocking in other compilers, so assume the worst case.
               return True;
            end if;

         elsif Scope_Name (2) = Name_Dispatching then
            return Scope_Name (3) = Name_Yield;

         elsif Scope_Name (2) = Name_Task_Identification then
            return Scope_Name (3) = Name_Abort_Task;

         elsif Scope_Name (2) = Name_Synchronous_Task_Control then

            if Scope_Name (3) = Name_Suspend_Until_True then
               return True;
            elsif Scope_Name (3) = Name_EDF then
               return Scope_Name (4) =
                 Name_Suspend_Until_True_And_Set_Deadline;
            else
               return False;
            end if;

         elsif Scope_Name (2) = Name_Synchronous_Barriers then
            return Scope_Name (3) = Name_Wait_For_Release;

         else
            --  All other predefined subprograms are nonblocking.
            return False;
         end if;

      end Is_Predefined_Potentially_Blocking;

      ----------
      -- Proc --
      ----------

      function Proc (N : Node_Id) return Traverse_Result is
      begin
         --  Detect a potentially blocking statement; RM 9.5.1 (8-16).
         --  The following check mirrors the callers of
         --  Check_Potentially_Blocking_Operation but immediately rejects
         --  all kinds of the select statement.
         case Nkind (N) is
            when N_Abort_Statement        |
                 N_Accept_Statement       |
                 N_Asynchronous_Select    |
                 N_Conditional_Entry_Call |
                 N_Delay_Statement        |
                 N_Selective_Accept       |
                 N_Timed_Entry_Call       =>

               Potentially_Blocking_Statement_Found := True;
               return Abandon;

            --  Front end rewrites external calls to protected procedures as
            --  entry calls. It is best to check the call convention.

            when N_Entry_Call_Statement =>

               if Convention (Entity (Selector_Name (Name (N)))) =
                 Convention_Entry
               then
                  Potentially_Blocking_Statement_Found := True;
                  return Abandon;
               else
                  return OK;
               end if;

            --  Predefined potentially blocking subprograms cannot be reliably
            --  detected in phase 2, where we only have entity names. Here
            --  we have full AST of their specifications and can precisely
            --  distinguish between blocking/nonblocking homonyms, e.g.
            --  Put/Get, by looking at the name of their first formal
            --  parameter. In phase 2 we only have names like "put__2"
            --  and "put__3".
            when N_Procedure_Call_Statement |
                 N_Function_Call =>

               if Is_Predefined_Potentially_Blocking (Get_Called_Entity (N))
               then
                  Potentially_Blocking_Statement_Found := True;
                  return Abandon;
               else
                  return OK;
               end if;

            when N_Object_Declaration =>
               --  ??? non-library-level task declarations should be already
               --  rejected by the Ravenscar profile restrictions.
               if Has_Task (Etype (Defining_Identifier (N))) then
                  Potentially_Blocking_Statement_Found := True;
                  return Abandon;
               else
                  return OK;
               end if;

            when others =>
               return OK;
         end case;
      end Proc;

   --  Start of processing for Has_Only_Nonblocking_Statements

   begin
      Traverse (N);
      return not Potentially_Blocking_Statement_Found;
   end Has_Only_Nonblocking_Statements;

   ------------------
   -- In_Main_Unit --
   ------------------

   function In_Main_Unit (N : Node_Id) return Boolean is
      Real_Node : constant Node_Id :=
        (if Is_Itype (N) then Associated_Node_For_Itype (N) else N);
   begin

      --  ??? Should be made more efficient

      return In_Main_Unit_Spec (Real_Node) or else
        In_Main_Unit_Body (Real_Node);
   end In_Main_Unit;

   -----------------------
   -- In_Main_Unit_Body --
   -----------------------

   function In_Main_Unit_Body (N : Node_Id) return Boolean is
      CU   : constant Node_Id := Enclosing_Lib_Unit_Node (N);
      Root : Node_Id;

   begin
      if No (CU) then
         return False;
      end if;

      Root := Unit (CU);

      case Nkind (Root) is
         when N_Package_Body    |
              N_Subprogram_Body =>

            return Is_Main_Cunit (Root);

         when N_Package_Declaration            |
              N_Generic_Package_Declaration    |
              N_Subprogram_Declaration         |
              N_Generic_Subprogram_Declaration =>

            return False;

         when N_Package_Renaming_Declaration           |
              N_Generic_Package_Renaming_Declaration   |
              N_Subprogram_Renaming_Declaration        |
              N_Generic_Function_Renaming_Declaration  |
              N_Generic_Procedure_Renaming_Declaration =>

            return False;

         when others =>
            raise Program_Error;
      end case;
   end In_Main_Unit_Body;

   -----------------------
   -- In_Main_Unit_Spec --
   -----------------------

   function In_Main_Unit_Spec (N : Node_Id) return Boolean is
      CU   : constant Node_Id := Enclosing_Lib_Unit_Node (N);
      Root : Node_Id;

   begin
      if No (CU) then
         return False;
      end if;

      Root := Unit (CU);

      case Nkind (Root) is
         when N_Package_Body    |
              N_Subprogram_Body =>

            return False;

         when N_Package_Declaration            |
              N_Generic_Package_Declaration    |
              N_Subprogram_Declaration         |
              N_Generic_Subprogram_Declaration =>

            return Is_Main_Cunit (Root)
              or else Is_Spec_Unit_Of_Main_Unit (Root);

         when N_Package_Renaming_Declaration           |
              N_Generic_Package_Renaming_Declaration   |
              N_Subprogram_Renaming_Declaration        |
              N_Generic_Function_Renaming_Declaration  |
              N_Generic_Procedure_Renaming_Declaration =>

            return False;

         when others =>
            raise Program_Error;
      end case;
   end In_Main_Unit_Spec;

   -----------------------------
   -- In_Private_Declarations --
   -----------------------------

   function In_Private_Declarations (Decl : Node_Id) return Boolean is
      N : Node_Id;

   begin
      if Present (Parent (Decl))
        and then Nkind (Parent (Decl)) = N_Package_Specification
      then
         N := First (Private_Declarations (Parent (Decl)));
         while Present (N) loop
            if Decl = N then
               return True;
            end if;
            Next (N);
         end loop;
      end if;

      return False;
   end In_Private_Declarations;

   ---------------
   -- Is_Action --
   ---------------

   function Is_Action (N : Node_Id) return Boolean
   is
      L : constant List_Id := List_Containing (N);
      P : constant Node_Id := Parent (N);
   begin
      if No (L) or else No (P) then
         return False;
      end if;

      case Nkind (P) is
         when N_Component_Association =>
            return L = Loop_Actions (P);
         when N_And_Then | N_Or_Else =>
            return L = Actions (P);
         when N_If_Expression =>
            return L = Then_Actions (P) or L = Else_Actions (P);
         when N_Case_Expression_Alternative =>
            return L = Actions (P);
         when N_Elsif_Part =>
            return L = Condition_Actions (P);
         when N_Iteration_Scheme =>
            return L = Condition_Actions (P);
         when N_Block_Statement =>
            return L = Cleanup_Actions (P);
         when N_Expression_With_Actions =>
            return L = Actions (P);
         when N_Freeze_Entity =>
            return L = Actions (P);
         when others =>
            return False;
      end case;
   end Is_Action;

   -------------------------
   -- Is_Declared_In_Unit --
   -------------------------

   --  Parameters of subprograms cannot be local to a unit.

   function Is_Declared_In_Unit
     (E     : Entity_Id;
      Scope : Entity_Id) return Boolean
   is
     (Enclosing_Package_Or_Subprogram (E) = Scope and then not Is_Formal (E));

   -----------------------------
   -- Is_Ignored_Pragma_Check --
   -----------------------------

   function Is_Ignored_Pragma_Check (N : Node_Id) return Boolean is
      Arg1 : constant Node_Id := First (Pragma_Argument_Associations (N));
      Arg2 : constant Node_Id := Next (Arg1);
   begin
      return Is_Pragma_Check (N, Name_Precondition)
               or else
             Is_Pragma_Check (N, Name_Pre)
               or else
             Is_Pragma_Check (N, Name_Postcondition)
               or else
             Is_Pragma_Check (N, Name_Post)
               or else
             Is_Pragma_Check (N, Name_Static_Predicate)
               or else
             Is_Pragma_Check (N, Name_Predicate)
               or else
             Is_Predicate_Function_Call (Get_Pragma_Arg (Arg2));
   end Is_Ignored_Pragma_Check;

   --------------------------
   -- Is_In_Analyzed_Files --
   --------------------------

   function Is_In_Analyzed_Files (E : Entity_Id) return Boolean is
      Encl_Unit : Node_Id;

   begin
      --  Retrieve the library unit containing E

      Encl_Unit := Enclosing_Lib_Unit_Node (E);

      --  case 1: the entity is neither in the spec or body compilation unit of
      --  the unit currently analyzed, so return False.

      if Cunit (Main_Unit) /= Encl_Unit
        and then Library_Unit (Cunit (Main_Unit)) /= Encl_Unit
      then
         return False;

      --  gnat2why is now only called on requested files, so here the result is
      --  always true

      else
         return True;
      end if;
   end Is_In_Analyzed_Files;

   ----------------------------------------
   -- Is_Local_Subprogram_Always_Inlined --
   ----------------------------------------

   function Is_Local_Subprogram_Always_Inlined
     (E : Entity_Id) return Boolean is
   begin
      --  A subprogram always inlined should have Body_To_Inline set and flag
      --  Is_Inlined_Always set to True.

      --  subprograms of protected objects are never inlined.

      return Is_Subprogram (E)
        and then Present (Subprogram_Spec (E))
        and then Present (Body_To_Inline (Subprogram_Spec (E)))
        and then Is_Inlined_Always (E)
        and then Convention (E) /= Convention_Protected;
   end Is_Local_Subprogram_Always_Inlined;

   -------------------
   -- Is_Main_Cunit --
   -------------------

   function Is_Main_Cunit (N : Node_Id) return Boolean is
     (Get_Cunit_Unit_Number (Parent (N)) = Main_Unit);

   -------------------
   -- Is_Null_Range --
   -------------------

   function Is_Null_Range (T : Entity_Id) return Boolean is
      (Is_Discrete_Type (T)
        and then Has_Static_Scalar_Subtype (T)
        and then Expr_Value (Low_Bound (Scalar_Range (T))) >
                 Expr_Value (High_Bound (Scalar_Range (T))));

   ----------------------
   -- Is_Others_Choice --
   ----------------------

   function Is_Others_Choice (Choices : List_Id) return Boolean is
   begin
      return List_Length (Choices) = 1
        and then Nkind (First (Choices)) = N_Others_Choice;
   end Is_Others_Choice;

   ----------------------
   -- Is_Package_State --
   ----------------------

   function Is_Package_State (E : Entity_Id) return Boolean is
      (Ekind (E) = E_Abstract_State
         or else
      (Ekind (E) = E_Variable
         and then Ekind (Scope (E)) in E_Package | E_Package_Body));

   ---------------
   -- Is_Pragma --
   ---------------

   function Is_Pragma (N : Node_Id; Name : Pragma_Id) return Boolean is
     (Nkind (N) = N_Pragma
       and then Get_Pragma_Id (Pragma_Name (N)) = Name);

   ----------------------------------
   -- Is_Pragma_Annotate_Gnatprove --
   ----------------------------------

   function Is_Pragma_Annotate_GNATprove (N : Node_Id) return Boolean is
     (Is_Pragma (N, Pragma_Annotate)
        and then
      Get_Name_String
        (Chars (Get_Pragma_Arg (First (Pragma_Argument_Associations (N)))))
      = "gnatprove");

   ------------------------------
   -- Is_Pragma_Assert_And_Cut --
   ------------------------------

   function Is_Pragma_Assert_And_Cut (N : Node_Id) return Boolean is
      Orig : constant Node_Id := Original_Node (N);

   begin
      return
        (Present (Orig) and then
         Is_Pragma (Orig, Pragma_Assert_And_Cut));
   end Is_Pragma_Assert_And_Cut;

   ---------------------
   -- Is_Pragma_Check --
   ---------------------

   function Is_Pragma_Check (N : Node_Id; Name : Name_Id) return Boolean is
     (Is_Pragma (N, Pragma_Check)
        and then
      Chars (Get_Pragma_Arg (First (Pragma_Argument_Associations (N))))
      = Name);

   --------------------------------
   -- Is_Predicate_Function_Call --
   --------------------------------

   function Is_Predicate_Function_Call (N : Node_Id) return Boolean is
     (Nkind (N) = N_Function_Call
      and then Is_Predicate_Function (Entity (Name (N))));

   ------------------------------
   -- Is_Quantified_Loop_Param --
   ------------------------------

   function Is_Quantified_Loop_Param (E : Entity_Id) return Boolean is
     (Present (Scope (E))
       and then Present (Parent (Scope (E)))
       and then Nkind (Parent (Scope (E))) = N_Quantified_Expression);

   -------------------------------------
   -- Is_Requested_Subprogram_Or_Task --
   -------------------------------------

   function Is_Requested_Subprogram_Or_Task (E : Entity_Id) return Boolean is
     (Ekind (E) in Subprogram_Kind | Task_Kind | E_Task_Body | Entry_Kind
        and then
      GP_Subp_Marker & To_String (Gnat2Why_Args.Limit_Subp) =
        SPARK_Util.Subp_Location (E));

   -------------------------------
   -- Is_Simple_Shift_Or_Rotate --
   -------------------------------

   function Is_Simple_Shift_Or_Rotate (E : Entity_Id) return Boolean is

      --  Define a convenient short hand for the test below
      function ECI (Left, Right : String) return Boolean
        renames Equal_Case_Insensitive;

   begin
      Get_Unqualified_Decoded_Name_String (Chars (E));

      declare
         Name : constant String := Name_Buffer (1 .. Name_Len);
      begin
         return  --  return True iff...

           --  it is an intrinsic
           Is_Intrinsic_Subprogram (E)

           --  modular type
           and then Is_Modular_Integer_Type (Etype (E))

           --  without functional contract
           and then not Has_Contracts (E, Name_Precondition)
           and then not Has_Contracts (E, Name_Postcondition)
           and then not Has_Contracts (E, Name_Contract_Cases)

           --  which corresponds to a shift or rotate
           and then
             (ECI (Name, Get_Name_String (Name_Shift_Right))
                or else
              ECI (Name,  Get_Name_String (Name_Shift_Right_Arithmetic))
                or else
              ECI (Name, Get_Name_String (Name_Shift_Left))
                or else
              ECI (Name, Get_Name_String (Name_Rotate_Left))
                or else
              ECI (Name, Get_Name_String (Name_Rotate_Right)));
      end;
   end Is_Simple_Shift_Or_Rotate;

   -------------------------------
   -- Is_Spec_Unit_Of_Main_Unit --
   -------------------------------

   function Is_Spec_Unit_Of_Main_Unit (N : Node_Id) return Boolean is
     (Present (Corresponding_Body (N))
       and then Is_Main_Cunit
        (Unit (Enclosing_Lib_Unit_Node (Corresponding_Body (N)))));

   ------------------------------
   -- Is_Standard_Boolean_Type --
   ------------------------------

   function Is_Standard_Boolean_Type (E : Entity_Id) return Boolean is
     (E = Standard_Boolean
        or else
     (Ekind (E) = E_Enumeration_Subtype
        and then Etype (E) = Standard_Boolean
        and then Scalar_Range (E) = Scalar_Range (Etype (E))));

   --------------------------
   -- Is_Static_Array_Type --
   --------------------------

   function Is_Static_Array_Type (E : Entity_Id) return Boolean is
     (Is_Array_Type (E)
       and then Is_Constrained (E)
       and then Has_Static_Array_Bounds (E));

   --------------------------------------
   -- Is_Unchecked_Conversion_Instance --
   --------------------------------------

   function Is_Unchecked_Conversion_Instance (E : Entity_Id) return Boolean is
      Conv : Entity_Id := Empty;

   begin
      if Present (Associated_Node (E))
        and then Present (Parent (Associated_Node (E)))
      then
         Conv := Generic_Parent (Parent (Associated_Node (E)));
      end if;

      return Present (Conv)
        and then Chars (Conv) = Name_Unchecked_Conversion
        and then Is_Predefined_File_Name
          (Unit_File_Name (Get_Source_Unit (Conv)))
        and then Is_Intrinsic_Subprogram (Conv);
   end Is_Unchecked_Conversion_Instance;

   ----------------------------
   -- Iterate_Call_Arguments --
   ----------------------------

   procedure Iterate_Call_Arguments (Call : Node_Id)
   is
      Params     : constant List_Id := Parameter_Associations (Call);
      Cur_Formal : Node_Id := First_Entity (Get_Called_Entity (Call));
      Cur_Actual : Node_Id := First (Params);
      In_Named   : Boolean := False;
   begin
      --  We have to deal with named arguments, but the frontend has
      --  done some work for us. All unnamed arguments come first and
      --  are given as-is, while named arguments are wrapped into a
      --  N_Parameter_Association. The field First_Named_Actual of the
      --  function or procedure call points to the first named argument,
      --  that should be inserted after the last unnamed one. Each
      --  Named Actual then points to a Next_Named_Actual. These
      --  pointers point directly to the actual, but Next_Named_Actual
      --  pointers are attached to the N_Parameter_Association, so to
      --  get the next actual from the current one, we need to follow
      --  the Parent pointer.
      --
      --  The Boolean In_Named states how to obtain the next actual:
      --  either follow the Next pointer, or the Next_Named_Actual of
      --  the parent.
      --  We start by updating the Cur_Actual and In_Named variables for
      --  the first parameter.

      if Nkind (Cur_Actual) = N_Parameter_Association then
         In_Named := True;
         Cur_Actual := First_Named_Actual (Call);
      end if;

      while Present (Cur_Formal) and then Present (Cur_Actual) loop
         Handle_Argument (Cur_Formal, Cur_Actual);
         Cur_Formal := Next_Formal (Cur_Formal);

         if In_Named then
            Cur_Actual := Next_Named_Actual (Parent (Cur_Actual));
         else
            Next (Cur_Actual);

            if Nkind (Cur_Actual) = N_Parameter_Association then
               In_Named := True;
               Cur_Actual := First_Named_Actual (Call);
            end if;
         end if;
      end loop;
   end Iterate_Call_Arguments;

   ----------------------------------
   -- Location_In_Standard_Library --
   ----------------------------------

   function Location_In_Standard_Library (Loc : Source_Ptr) return Boolean is
   begin
      if Loc = No_Location then
         return False;
      end if;

      return
        Loc in Standard_Location | Standard_ASCII_Location | System_Location
        or else Unit_In_Standard_Library (Unit (Get_Source_File_Index (Loc)));
   end Location_In_Standard_Library;

   -------------------
   -- Might_Be_Main --
   -------------------

   function Might_Be_Main (E : Entity_Id) return Boolean is
     (Scope (E) = Standard_Standard and then No (First_Formal (E)));
     --  ??? Is this expression equivalent to test in
     --  Sem_Ch13.Analyze_Pragma.Check_In_Main_Program ?

   --------------------
   -- Nth_Index_Type --
   --------------------

   function Nth_Index_Type (E : Entity_Id; Dim : Positive) return Node_Id is
      Cur   : Positive := 1;
      Index : Node_Id := First_Index (E);

   begin
      if Ekind (E) = E_String_Literal_Subtype then
         return E;
      end if;

      while Cur /= Dim loop
         Cur := Cur + 1;
         Next_Index (Index);
      end loop;

      return Etype (Index);
   end Nth_Index_Type;

   ------------------------------------
   -- Number_Of_Assocs_In_Expression --
   ------------------------------------

   function Number_Of_Assocs_In_Expression (N : Node_Id) return Natural is
      Count : Natural := 0;

      function Find_Assoc (N : Node_Id) return Traverse_Result;
      --  Increments Count if N is a N_Component_Association

      ----------------
      -- Find_Assoc --
      ----------------

      function Find_Assoc (N : Node_Id) return Traverse_Result is
      begin
         case Nkind (N) is
            when N_Component_Association =>
               Count := Count + 1;
            when others => null;
         end case;
         return OK;
      end Find_Assoc;

      procedure Count_Assoc is new Traverse_Proc (Find_Assoc);

   --  Start of processing for Number_Of_Assocs_In_Expression

   begin
      Count_Assoc (N);
      return Count;
   end Number_Of_Assocs_In_Expression;

   -------------
   -- PO_Body --
   -------------

   function PO_Body (E : Entity_Id) return Node_Id is
      Ptr : constant Node_Id := Parent (E);

   begin
      pragma Assert (Nkind (Ptr) = N_Protected_Type_Declaration);
      return Parent (Corresponding_Body (Ptr));
   end PO_Body;

   -------------------
   -- PO_Definition --
   -------------------

   function PO_Definition (E : Entity_Id) return Node_Id is
      Ptr : constant Node_Id := Parent (E);

   begin
      pragma Assert (Nkind (Ptr) = N_Protected_Type_Declaration);
      return Protected_Definition (Ptr);
   end PO_Definition;

   ---------------------------
   -- Root_Record_Component --
   ---------------------------

   function Root_Record_Component (E : Entity_Id) return Entity_Id is
      Rec_Type : constant Entity_Id := Retysp (Scope (E));
      Root     : constant Entity_Id := Root_Record_Type (Rec_Type);

   begin
      --  If E is the component of a root type, return it

      if Root = Rec_Type then
         return E;
      end if;

      --  In the component case, it is enough to simply search for the matching
      --  component in the root type, using "Chars".

      if Ekind (E) = E_Component then
         return Search_Component_By_Name (Root, E);
      end if;

      --  In the discriminant case, we need to climb up the hierarchy of types,
      --  to get to the corresponding discriminant in the root type. Note that
      --  there can be more than one corresponding discriminant (because of
      --  renamings), in this case the frontend has picked one for us.

      pragma Assert (Ekind (E) = E_Discriminant);

      declare
         Cur_Type : Entity_Id := Rec_Type;
         Comp     : Entity_Id := E;

      begin
         --  Throughout the loop, maintain the invariant that Comp is a
         --  component of Cur_Type.

         while Cur_Type /= Root loop

            --  If the discriminant Comp constrains a discriminant of the
            --  parent type, then locate the corresponding discriminant of the
            --  parent type by calling Corresponding_Discriminant. This is
            --  needed because both discriminants may not have the same name.

            if Present (Corresponding_Discriminant (Comp)) then
               Comp     := Corresponding_Discriminant (Comp);
               Cur_Type := Scope (Comp);

            --  Otherwise, just climb the type derivation/subtyping chain

            else
               declare
                  Old_Type : constant Entity_Id := Cur_Type;
               begin
                  Cur_Type := Retysp (Etype (Cur_Type));
                  pragma Assert (Cur_Type /= Old_Type);
                  Comp := Search_Component_By_Name (Cur_Type, Comp);
               end;
            end if;
         end loop;

         return Comp;
      end;
   end Root_Record_Component;

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

      return Result;
   end Root_Record_Type;

   ------------------------------
   -- Search_Component_By_Name --
   ------------------------------

   function Search_Component_By_Name
     (Rec  : Entity_Id;
      Comp : Entity_Id) return Entity_Id
   is
      Specific_Rec : constant Entity_Id :=
        (if Is_Class_Wide_Type (Rec)
         then Retysp (Get_Specific_Type_From_Classwide (Rec))
         else Rec);
      Cur_Comp     : Entity_Id :=
        First_Component_Or_Discriminant (Specific_Rec);
   begin
      while Present (Cur_Comp) loop
         if Chars (Cur_Comp) = Chars (Comp) then
            return Cur_Comp;
         end if;

         Next_Component_Or_Discriminant (Cur_Comp);
      end loop;

      return Empty;
   end Search_Component_By_Name;

   -----------------
   -- Source_Name --
   -----------------

   function Source_Name (E : Entity_Id) return String is

      function Short_Name (E : Entity_Id) return String;
      --  @return the uncapitalized unqualified name for E

      ----------------
      -- Short_Name --
      ----------------

      function Short_Name (E : Entity_Id) return String is
      begin
         Get_Unqualified_Name_String (Chars (E));
         return Name_Buffer (1 .. Name_Len);
      end Short_Name;

   --  Start of processing for Source_Name

   begin
      if E = Empty then
         return "";
      end if;

      declare
         Name : String := Short_Name (E);
         Loc  : Source_Ptr := Sloc (E);
         Buf  : Source_Buffer_Ptr;
      begin
         if Name /= "" and then Loc >= First_Source_Ptr then
            Buf := Source_Text (Get_Source_File_Index (Loc));

            --  Copy characters from source while they match (modulo
            --  capitalization) the name of the entity.

            for Idx in Name'Range loop
               exit when not Identifier_Char (Buf (Loc))
                 or else Fold_Lower (Buf (Loc)) /= Name (Idx);
               Name (Idx) := Buf (Loc);
               Loc := Loc + 1;
            end loop;
         end if;

         return Name;
      end;
   end Source_Name;

   --------------------
   -- Spec_File_Name --
   --------------------

   function Spec_File_Name (N : Node_Id) return String is
      CU : Node_Id := Enclosing_Lib_Unit_Node (N);

   begin
      case Nkind (Unit (CU)) is
         when N_Package_Body =>
            CU := Library_Unit (CU);
         when others =>
            null;
      end case;

      return File_Name (Sloc (CU));
   end Spec_File_Name;

   -----------------------------------
   -- Spec_File_Name_Without_Suffix --
   -----------------------------------

   function Spec_File_Name_Without_Suffix (N : Node_Id) return String is
     (File_Name_Without_Suffix (Spec_File_Name (N)));

   -------------------------
   -- Static_Array_Length --
   -------------------------

   function Static_Array_Length (E : Entity_Id; Dim : Positive) return Uint is
      F_Index : constant Entity_Id := Nth_Index_Type (E, Dim);

   begin
      if Ekind (E) = E_String_Literal_Subtype then
         return String_Literal_Length (E);
      else
         declare
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

   --------------------
   -- String_Of_Node --
   --------------------

   function String_Of_Node (N : Node_Id) return String is

      function Real_Image (U : Ureal) return String;
      function String_Image (S : String_Id) return String;
      function Ident_Image (Expr        : Node_Id;
                            Orig_Expr   : Node_Id;
                            Expand_Type : Boolean)
                            return String;

      function Node_To_String is new
        Expression_Image (Real_Image, String_Image, Ident_Image);
      --  The actual printing function

      -----------------
      -- Ident_Image --
      -----------------

      function Ident_Image (Expr        : Node_Id;
                            Orig_Expr   : Node_Id;
                            Expand_Type : Boolean)
                            return String
      is
         pragma Unreferenced (Orig_Expr, Expand_Type);
      begin
         if Nkind (Expr) = N_Defining_Identifier then
            return Source_Name (Expr);
         elsif Present (Entity (Expr)) then
            return Source_Name (Entity (Expr));
         else
            return Get_Name_String (Chars (Expr));
         end if;
      end Ident_Image;

      ----------------
      -- Real_Image --
      ----------------

      function Real_Image (U : Ureal) return String is
      begin
         pragma Unreferenced (U);
         --  ??? still to be done
         return "";
      end Real_Image;

      ------------------
      -- String_Image --
      ------------------

      function String_Image (S : String_Id) return String is
      begin
         Name_Len := 0;
         Add_Char_To_Name_Buffer ('"');
         Add_String_To_Name_Buffer (S);
         Add_Char_To_Name_Buffer ('"');
         return Name_Buffer (1 .. Name_Len);
      end String_Image;

   --  Start of processing for String_Of_Node

   begin
      return Node_To_String (N, "");
   end String_Of_Node;

   -------------------
   -- Subp_Location --
   -------------------

   function Subp_Location (E : Entity_Id) return String is
      S : constant Subp_Type := Entity_To_Subp (E);
      B : constant Base_Sloc := Subp_Sloc (S).First_Element;

   begin
      --  ??? Probably need to change this code to take M412-032 into account

      return GP_Subp_Marker & Base_Sloc_File (B) & ":" & Image (B.Line, 1);
   end Subp_Location;

   ---------------------------------
   -- Subprogram_Full_Source_Name --
   ---------------------------------

   function Subprogram_Full_Source_Name (E : Entity_Id) return String is
      Name : constant String := Source_Name (E);

   begin
      if Has_Fully_Qualified_Name (E)
        or else Scope (E) = Standard_Standard
      then
         return Name;
      else
         return Subprogram_Full_Source_Name (Unique_Entity (Scope (E))) &
           "." & Name;
      end if;
   end Subprogram_Full_Source_Name;

   -------------------------------------
   -- Subprogram_Is_Ignored_For_Proof --
   -------------------------------------

   --  Functions generated by the frontend for aspects Type_Invariant and
   --  Default_Initial_Condition should be ignored. This does not include
   --  the functions generated for Predicate aspects, as these functions are
   --  translated to check absence of RTE in the predicate in the most general
   --  context.

   function Subprogram_Is_Ignored_For_Proof (E : Entity_Id) return Boolean is
     (Ekind (E) in E_Function | E_Procedure and then
       (Is_Invariant_Procedure (E)
          or else
        Is_Default_Init_Cond_Procedure (E)));

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

   --------------
   -- Get_Body --
   --------------

   function Get_Body (E : Entity_Id) return Node_Id is
   begin
      return (case Ekind (E) is
              when E_Entry => Entry_Body (E),
              when E_Task_Type => Task_Body (E),
              when Subprogram_Kind => Subprogram_Body (E),
              when others => raise Program_Error);
   end Get_Body;

   ---------------------
   -- Get_Body_Entity --
   ---------------------

   function Get_Body_Entity (E : Entity_Id) return Entity_Id is
   begin
      return (case Ekind (E) is
              when E_Entry => Entry_Body_Entity (E),
              when E_Task_Type => Task_Body_Entity (E),
              when Subprogram_Kind => Subprogram_Body_Entity (E),
              when others => raise Program_Error);
   end Get_Body_Entity;

end SPARK_Util;
