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

with Ada.Strings;               use Ada.Strings;
with Ada.Strings.Equal_Case_Insensitive;
with Assumption_Types;          use Assumption_Types;
with Csets;                     use Csets;
with Elists;                    use Elists;
with Flow_Types;                use Flow_Types;
with Flow_Utility;              use Flow_Utility;
with Fname;                     use Fname;
with GNAT.Directory_Operations; use GNAT.Directory_Operations;

with SPARK_Definition;          use SPARK_Definition;

with Gnat2Why_Args;
with Gnat2Why.Assumptions;      use Gnat2Why.Assumptions;
with GNATCOLL.Utils;            use GNATCOLL.Utils;
with Nlists;                    use Nlists;
with Sem_Aux;                   use Sem_Aux;
with Sem_Disp;                  use Sem_Disp;
with Sem_Eval;                  use Sem_Eval;
with Exp_Util;                  use Exp_Util;
with Pprint;                    use Pprint;
with Stand;                     use Stand;
with Stringt;                   use Stringt;
with String_Utils;              use String_Utils;
with Treepr;                    use Treepr;
with Urealp;                    use Urealp;

package body SPARK_Util is

   function Is_Main_Cunit (N : Node_Id) return Boolean;
   function Is_Spec_Unit_Of_Main_Unit (N : Node_Id) return Boolean;

   ------------------
   -- Global State --
   ------------------

   Full_To_Partial_Entities : Node_Maps.Map;
   --  Map from full views of entities to their partial views, for deferred
   --  constants and private types.

   Classwide_To_Tagged_Entities : Node_Maps.Map;
   --  Map from classwide types to the corresponding specific tagged type

   -----------------------------
   -- Add_Classwide_To_Tagged --
   -----------------------------

   procedure Add_Classwide_To_Tagged (Classwide, Ty : Entity_Id) is
      Typ : Entity_Id := Ty;
   begin

      --  Use partial view for type with fullview not in SPARK

      if Full_To_Partial_Entities.Contains (Ty)
        and then Fullview_Not_In_SPARK (Full_To_Partial_Entities.Element (Ty))
      then
         Typ := Full_To_Partial_Entities.Element (Ty);
      end if;

      Classwide_To_Tagged_Entities.Insert (Classwide, Typ);
   end Add_Classwide_To_Tagged;

   -------------------------------
   -- Add_Full_And_Partial_View --
   -------------------------------

   procedure Add_Full_And_Partial_View (Full, Partial : Entity_Id) is
   begin
      Full_To_Partial_Entities.Insert (Full, Partial);
   end Add_Full_And_Partial_View;

   ------------------------------------
   -- Aggregate_Is_Fully_Initialized --
   ------------------------------------

   function Aggregate_Is_Fully_Initialized (N : Node_Id) return Boolean is

      procedure Skip_Ancestor_And_Generated_Components
        (Component : in out Entity_Id);
      --  If Component is either a component belonging to an ancestor
      --  or a compiler generated component, skip it and all similar
      --  following components.

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
            if No (Ancestor_Part (N)) then
               return False;
            end if;

            Ancestor_Typ  := MUT (Etype (Ancestor_Part (N)));
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

      Typ         : constant Entity_Id := MUT (Etype (N));
      Assocs      : List_Id;
      Component   : Entity_Id;
      Association : Node_Id;
      Not_Init    : constant Boolean :=
        Default_Initialization (Typ) /= Full_Default_Initialization;

   --  Start of Aggregate_Is_Fully_Initialized

   begin
      if Is_Record_Type (Typ) then
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

   ------------------------------------------
   -- All_Aggregates_Are_Fully_Initialized --
   ------------------------------------------

   function All_Aggregates_Are_Fully_Initialized
     (N : Node_Id) return Boolean
   is
      Aggregate_Not_Fully_Initialized : Boolean := False;

      function Check_Aggregate (N : Node_Id) return Traverse_Result;
      --  Set Aggregate_Not_Fully_Initialized to True if N is an aggregate not
      --  fully initialized.

      ---------------------
      -- Check_Aggregate --
      ---------------------

      function Check_Aggregate (N : Node_Id) return Traverse_Result is
      begin
         if Nkind (N) = N_Aggregate
           and then not Aggregate_Is_Fully_Initialized (N)
         then
            Aggregate_Not_Fully_Initialized := True;
            return Abandon;
         else
            return OK;
         end if;
      end Check_Aggregate;

      function Traverse_Aggregate is new Traverse_Func (Check_Aggregate);

      Ignored : Traverse_Final_Result;
      pragma Unreferenced (Ignored);

   begin
      Ignored := Traverse_Aggregate (N);
      return not Aggregate_Not_Fully_Initialized;
   end All_Aggregates_Are_Fully_Initialized;

   ------------------------
   -- Analysis_Requested --
   ------------------------

   function Analysis_Requested (E : Entity_Id) return Boolean is
   begin
      return Is_In_Analyzed_Files (E)

       --  Either the analysis is requested for the complete unit, or if it is
       --  requested for a specific subprogram, check whether it is E.

        and then (Gnat2Why_Args.Limit_Subp = Null_Unbounded_String
                    or else
                  Is_Requested_Subprogram (E))

        --  Ignore inlined subprograms that are referenced. Unreferenced
        --  subprograms are analyzed anyway, as they are likely to correspond
        --  to an intermediate stage of development. Also always analyze the
        --  subprogram if analysis was specifically requested for it.

        and then (not Is_Local_Subprogram_Always_Inlined (E)
                    or else
                  not Referenced (E)
                    or else
                  Is_Requested_Subprogram (E));
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
      CU       : Node_Id := Enclosing_Comp_Unit_Node (N);
      Switch   : Boolean := False;
   begin
      case Nkind (Unit (CU)) is
         when N_Package_Body    |
              N_Subprogram_Body |
              N_Subunit         =>
            null;
         when others =>
            Switch := True;
      end case;
      if Switch and then Present (Library_Unit (CU)) then
         CU := Library_Unit (CU);
      end if;
      return File_Name (Sloc (CU));
   end Body_File_Name;

   --------------------------------
   -- Check_Needed_On_Conversion --
   --------------------------------

   function Check_Needed_On_Conversion (From, To : Entity_Id) return Boolean is
   begin
      --  No check needed if same type

      if To = From then
         return False;

      --  No check needed when converting to base type

      elsif To = Etype (From) then
         return False;

      --  Converting to unconstrained record types does not require a check
      --  on conversion. The needed check is inserted by the frontend using
      --  an explicit exception.

      elsif Is_Record_Type (To) and then not Is_Constrained (To) then
         return False;
      end if;

      return True;
   end Check_Needed_On_Conversion;

   -----------------------------------
   -- Component_Is_Visible_In_SPARK --
   -----------------------------------

   function Component_Is_Visible_In_SPARK (E : Entity_Id) return Boolean is
      O : constant Entity_Id := Original_Record_Component (E);
      Original_Record : constant Entity_Id := Scope (O);
   begin
      if Ekind (E) in E_Discriminant then
         return True;
      else
         return Entity_In_SPARK (Original_Record)
           and then not Fullview_Not_In_SPARK (Original_Record);
      end if;
   end Component_Is_Visible_In_SPARK;

   --------------------------
   -- Corresponding_Tagged --
   --------------------------

   function Corresponding_Tagged (Classwide : Entity_Id) return Entity_Id is
     (Classwide_To_Tagged_Entities.Element (Classwide));

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
      if Is_Record_Type (E) then
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

      if Is_Private_Type (E) then
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

      if Number_Discriminants (E) > Natural'(0) then
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
      Explicit_Only : Boolean    := False)
      return Default_Initialization_Kind
   is
      Init : Default_Initialization_Kind;

      FDI : Boolean := False;
      NDI : Boolean := False;
      --  Two flags used to designate whether a record type has at least one
      --  fully default initialized component and/or one not fully default
      --  initialized component.

      procedure Process_Component (Rec_Prot_Comp : Entity_Id);
      --  Process component Rec_Prot_Comp of a record or protected type

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

   --  Start of Default_Initialization

   begin
      --  For types that are not in SPARK we trust the declaration.
      --  This means that if we find a Default_Initial_Condition
      --  aspect we trust it.

      if (not Entity_In_SPARK (Typ)
            or else Fullview_Not_In_SPARK (Typ))
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
           and then Etype (B_Type) /= B_Type
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

            if Present (Pragma_Argument_Associations (Prag)) then
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
            Type_Def : constant Node_Id := Type_Definition (Parent (Typ));
            Rec_Part : constant Node_Id := Record_Extension_Part (Type_Def);
         begin
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

         if Type_Based_On_External_Axioms (Typ) then
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

   -------------------------------
   -- Entity_In_External_Axioms --
   -------------------------------

   function Entity_In_External_Axioms (E : Entity_Id) return Boolean is
   begin
      --  ??? Ideally this should be a precondition of the function, and it
      --  should only be called on non Empty entities

      if No (E) then
         return False;
      end if;

      return Present
        (Containing_Package_With_Ext_Axioms (E));
   end Entity_In_External_Axioms;

   --------------------------------------
   -- Expression_Functions_All_The_Way --
   --------------------------------------

   function Expression_Functions_All_The_Way (E : Entity_Id) return Boolean is

      Only_Expression_Functions : Boolean := True;
      --  Set to False if a call to something else than an expression
      --  function is seen.

      Already_Seen : Node_Sets.Set;
      --  Set of functions already seen

      use Node_Sets;

      function Mark_Regular_Call (N : Node_Id) return Traverse_Result;
      --  Basic marking function

      procedure Traverse_Expression_Function (E : Entity_Id);
      --  Main recursive traversal

      -----------------------
      -- Mark_Regular_Call --
      -----------------------

      function Mark_Regular_Call (N : Node_Id) return Traverse_Result is
      begin
         if Nkind_In (N, N_Function_Call, N_Procedure_Call_Statement) then
            declare
               Nam : constant Node_Id := Name (N);
            begin
               if not Is_Entity_Name (Nam)
                 or else No (Entity (Nam))
               then
                  Only_Expression_Functions := False;
               else
                  Traverse_Expression_Function (Entity (Nam));
               end if;
            end;
         end if;
         return OK;
      end Mark_Regular_Call;

      procedure Traverse_And_Mark is new Traverse_Proc (Mark_Regular_Call);

      ----------------------------------
      -- Traverse_Expression_Function --
      ----------------------------------

      procedure Traverse_Expression_Function (E : Entity_Id) is
         Decl      : Node_Id;
         Body_Decl : Node_Id;

      begin
         if Nkind (Parent (E)) = N_Defining_Program_Unit_Name then
            Decl := Parent (Parent (Parent (E)));
         else
            Decl := Parent (Parent (E));
         end if;

         if Nkind (Decl) = N_Subprogram_Body then
            Body_Decl := Decl;
         elsif Present (Corresponding_Body (Decl)) then
            Body_Decl := Parent (Parent (Corresponding_Body (Decl)));
         else
            Body_Decl := Empty;
         end if;

         --  If not possible to follow calls to expression functions further
         --  because function is declared in another unit, consider it may not
         --  be an expression function.

         if No (Body_Decl) then
            Only_Expression_Functions := False;

         elsif Nkind (Original_Node (Decl)) /= N_Expression_Function
           and then Nkind (Original_Node (Body_Decl)) /= N_Expression_Function
         then
            Only_Expression_Functions := False;

         --  Protect against recursion, which cannot introduce more calls

         elsif Contains (Already_Seen, E) then
            null;

         else
            Include (Already_Seen, E);
            Traverse_And_Mark (Parent (Parent (Corresponding_Body (Decl))));
         end if;
      end Traverse_Expression_Function;

   begin
      Traverse_Expression_Function (E);
      return Only_Expression_Functions;
   end Expression_Functions_All_The_Way;

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
               if Present (Get_Subprogram_Body (E)) then
                  C := Contract (Defining_Entity (Specification
                                 (Get_Subprogram_Body (E))));
               else
                  C := Empty;
               end if;
            end if;

            if No (C) then
               P := Empty;
            elsif Name = Name_Precondition then
               P := Pre_Post_Conditions (C);
            elsif Name = Name_Postcondition then
               P := Pre_Post_Conditions (C);
            elsif Name = Name_Refined_Post then
               P := Pre_Post_Conditions (C);
            elsif Name = Name_Initial_Condition then
               P := Classifications (C);
            else
               P := Contract_Test_Cases (C);
            end if;

            while Present (P) loop
               if Chars (Pragma_Identifier (P)) = Name
                 and then Classwide = Class_Present (P)
               then
                  Contracts.Append
                    (Expression (First (Pragma_Argument_Associations (P))));
               end if;

               P := Next_Pragma (P);
            end loop;

            return Contracts;

         when Name_Global | Name_Depends =>
            raise Why.Not_Implemented;

         when others =>
            raise Program_Error;
      end case;
   end Find_Contracts;

   ------------------------
   -- First_Discriminant --
   ------------------------

   function First_Discriminant (Id : E) return E is
      Comp_Id : E := First_Entity (Id);

   begin
      Comp_Id := First_Entity (Id);
      while Present (Comp_Id) loop
         exit when Ekind (Comp_Id) = E_Discriminant;
         Comp_Id := Next_Entity (Comp_Id);
      end loop;

      return Comp_Id;
   end First_Discriminant;

   ---------------
   -- Full_Name --
   ---------------

   function Full_Name (N : Entity_Id) return String is
   begin
      --  In special cases, return a fixed name. These cases should match those
      --  for which Full_Name_Is_Not_Unique_Name returns True.

      if Full_Name_Is_Not_Unique_Name (N) then
         if Is_Standard_Boolean_Type (N) then
            return "bool";
         elsif N = Universal_Fixed then
            return "real";
         else
            raise Program_Error;
         end if;

      --  In the general case, return a name based on the Unique_Name

      else
         declare
            S : String := Unique_Name (N);
         begin

            --  In Why3, enumeration literals need to be upper case. Why2
            --  doesn't care, so we enforce upper case here

            if Ekind (N) = E_Enumeration_Literal then
               Capitalize_First (S);
            end if;
            return S;
         end;
      end if;
   end Full_Name;

   ----------------------------------
   -- Full_Name_Is_Not_Unique_Name --
   ----------------------------------

   function Full_Name_Is_Not_Unique_Name (N : Entity_Id) return Boolean is
   begin
      return Is_Standard_Boolean_Type (N) or else N = Universal_Fixed;
   end Full_Name_Is_Not_Unique_Name;

   --------------------
   -- Get_Abend_Kind --
   --------------------

   function Get_Abend_Kind
     (E          : Entity_Id;
      GG_Allowed : Boolean := True) return Execution_Kind_T
   is
   begin
      if Has_No_Output (E, GG_Allowed) then
         return Abnormal_Termination;
      else
         return Infinite_Loop;
      end if;
   end Get_Abend_Kind;

   --------------
   -- Get_Body --
   --------------

   function Get_Body_Entity (E : Entity_Id) return Entity_Id
   is
      Body_N : constant Node_Id := Sem_Util.Get_Subprogram_Body (E);

      Ptr : Node_Id;
   begin
      if No (Body_N) or else Nkind (Body_N) /= N_Subprogram_Body then
         return Empty;
      end if;

      if Acts_As_Spec (Body_N) then
         return Empty;
      end if;

      Ptr := Specification (Body_N);
      pragma Assert (Present (Ptr)
                       and then Nkind (Ptr) in N_Subprogram_Specification);

      Ptr := Defining_Unit_Name (Ptr);
      pragma Assert (Present (Ptr)
                       and then Nkind (Ptr) in N_Entity);

      return Ptr;
   end Get_Body_Entity;

   ----------------------------------------
   -- Get_Cursor_Type_In_Iterable_Aspect --
   ----------------------------------------

   function Get_Cursor_Type_In_Iterable_Aspect
     (Typ : Entity_Id) return Entity_Id is
   begin
      return Etype (Get_Iterable_Type_Primitive (Typ, Name_First));
   end Get_Cursor_Type_In_Iterable_Aspect;

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

   --------------------------------
   -- Get_Default_Init_Cond_Proc --
   --------------------------------

   function Get_Default_Init_Cond_Proc (E : Entity_Id) return Entity_Id is
      Base : constant Entity_Id :=
        (if Ekind (E) in Subtype_Kind then Etype (E) else E);
   begin
      return Default_Init_Cond_Procedure (Base);
   end Get_Default_Init_Cond_Proc;

   -----------------------------------------
   -- Get_Element_Type_In_Iterable_Aspect --
   -----------------------------------------

   function Get_Element_Type_In_Iterable_Aspect
     (Typ : Entity_Id) return Entity_Id is
   begin
      return Etype (Get_Iterable_Type_Primitive (Typ, Name_First));
   end Get_Element_Type_In_Iterable_Aspect;

   -------------------
   -- Get_Enclosing --
   -------------------

   function Get_Enclosing (N : Node_Id; K : Node_Kind) return Node_Id
   is
      Ptr : Node_Id := N;
   begin
      while Present (Ptr) and then Nkind (Ptr) /= K loop
         Ptr := Parent (Ptr);
      end loop;
      return Ptr;
   end Get_Enclosing;

   -------------------------------
   -- Get_Enclosing_Declaration --
   -------------------------------

   function Get_Enclosing_Declaration (N : Node_Id) return Node_Id is
      Decl_N : Node_Id := N;
   begin
      while Present (Decl_N)
        and then not (Nkind (Decl_N) in N_Declaration
                        or else
                      Nkind (Decl_N) in N_Later_Decl_Item)
      loop
         Decl_N := Parent (Decl_N);
      end loop;
      return Decl_N;
   end Get_Enclosing_Declaration;

   ------------------------
   -- Get_Enclosing_Unit --
   ------------------------

   function Get_Enclosing_Unit (E : Entity_Id) return Entity_Id is
      S : Entity_Id;
   begin
      S := Scope (E);
      loop
         if No (S) then
            return Empty;
         elsif Ekind_In (S, E_Package, E_Package_Body,
                      E_Generic_Package)
         then
            return S;
         elsif Ekind (S) in Subprogram_Kind then
            return S;
         else
            S := Scope (S);
         end if;
      end loop;
   end Get_Enclosing_Unit;

   -----------------------------------
   -- Get_Expr_From_Check_Only_Proc --
   -----------------------------------

   function Get_Expr_From_Check_Only_Proc (E : Entity_Id) return Node_Id is
      Body_N : constant Node_Id := Get_Subprogram_Body (E);
      Stmts  : constant List_Id :=
        Statements (Handled_Statement_Sequence (Body_N));
      Stmt   : Node_Id := First (Stmts);
      Arg    : Node_Id;
   begin
      while Present (Stmt) loop

         --  Return the second argument of the first pragma Check in the
         --  declaration list if any.

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

   -----------------------------
   -- Get_Expression_Function --
   -----------------------------

   function Get_Expression_Function (E : Entity_Id) return Node_Id is
      Decl_N : constant Node_Id := Parent (Get_Subprogram_Spec (E));
      Body_N : constant Node_Id := Get_Subprogram_Body (E);
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

      Par : constant Node_Id := Parent (Actual);

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
     (P      : Node_Id;
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
                         The_Global : Entity_Id)
      is
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

   --  Start of Get_Global_Items

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

   -------------------
   -- Get_Low_Bound --
   -------------------

   function Get_Low_Bound (E : Entity_Id) return Node_Id is
   begin
      if Ekind (E) = E_String_Literal_Subtype then
         return String_Literal_Low_Bound (E);
      else
         return Low_Bound (Scalar_Range (E));
      end if;
   end Get_Low_Bound;

   ----------------------
   -- Get_Package_Body --
   ----------------------

   function Get_Package_Body (E : Entity_Id) return Node_Id is
      N : Node_Id;
   begin
      N := Get_Package_Decl (E);

      if Present (Corresponding_Body (N)) then
         N := Parent (Corresponding_Body (N));

         if Nkind (N) = N_Defining_Program_Unit_Name then
            N := Parent (N);
         end if;
      else
         N := Empty;
      end if;

      return N;
   end Get_Package_Body;

   ----------------------
   -- Get_Package_Decl --
   ----------------------

   function Get_Package_Decl (E : Entity_Id) return Node_Id is
      (Parent (Get_Package_Spec (E)));

   ----------------------
   -- Get_Package_Spec --
   ----------------------

   function Get_Package_Spec (E : Entity_Id) return Node_Id is
      N : Node_Id;

   begin
      N := Parent (E);

      if Nkind (N) = N_Defining_Program_Unit_Name then
         N := Parent (N);
      end if;

      return N;
   end Get_Package_Spec;

   ---------------------------------
   -- Get_Procedure_Specification --
   ---------------------------------

   function Get_Procedure_Specification (E : Entity_Id) return Node_Id is
      N : Node_Id;
   begin
      N := Parent (E);
      case Nkind (N) is
         when N_Defining_Program_Unit_Name =>
            return Parent (N);
         when N_Procedure_Specification =>
            return N;
         when others =>
            raise Program_Error;
      end case;
   end Get_Procedure_Specification;

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

   -----------------------
   -- Get_Return_Object --
   -----------------------

   function Get_Return_Object_Entity (Stmt : Node_Id) return Entity_Id is
      Decl : Node_Id := First (Return_Object_Declarations (Stmt));
   begin
      while Present (Decl) loop
         exit when
           Is_Return_Object (Defining_Identifier (Decl));
         Next (Decl);
      end loop;
      pragma Assert (Present (Decl));
      return Defining_Identifier (Decl);
   end Get_Return_Object_Entity;
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

   -------------------------
   -- Get_Subprogram_Body --
   -------------------------

   --  Replace version in Sem_Util with this simpler one ???

   function Get_Subprogram_Body (E : Entity_Id) return Node_Id is
      Body_E : Entity_Id;
      N      : Node_Id;

   begin
      --  Retrieve the declaration for E

      N := Parent (Get_Subprogram_Spec (E));

      --  If this declaration is not a subprogram body, then it must be a
      --  subprogram declaration, from which we can retrieve the entity
      --  for the corresponding subprogram body.

      if Nkind (N) = N_Subprogram_Body then
         Body_E := E;
      else
         Body_E := Corresponding_Body (N);
      end if;

      --  If no body is available, return Empty

      if No (Body_E) then
         return Empty;

      --  Otherwise, retrieve the subprogram body

      else
         return Parent (Get_Subprogram_Spec (Body_E));
      end if;
   end Get_Subprogram_Body;

   -----------------------------------
   -- Get_Subprogram_Contract_Cases --
   -----------------------------------

   function Get_Subprogram_Contract_Cases (E : Entity_Id) return Node_Id is
      Prag : Node_Id;
   begin
      if Present (Contract (E)) then
         Prag := Contract_Test_Cases (Contract (E));
      else
         Prag := Empty;
      end if;

      while Present (Prag) loop
         if Pragma_Name (Prag) = Name_Contract_Cases then
            return Prag;
         end if;
         Prag := Next_Pragma (Prag);
      end loop;
      return Empty;
   end Get_Subprogram_Contract_Cases;

   -------------------------
   -- Get_Subprogram_Decl --
   -------------------------

   function Get_Subprogram_Decl (E : Entity_Id) return Node_Id is
      N : Node_Id;

   begin
      --  Retrieve the declaration for E

      N := Parent (Get_Subprogram_Spec (E));

      --  This declaration is either subprogram declaration or a subprogram
      --  body, in which case return Empty.

      if Nkind (N) = N_Subprogram_Declaration then
         return N;
      else
         return Empty;
      end if;
   end Get_Subprogram_Decl;

   -------------------------
   -- Get_Subprogram_Spec --
   -------------------------

   function Get_Subprogram_Spec (E : Entity_Id) return Node_Id is
      N : Node_Id;

   begin
      N := Parent (E);

      if Nkind (N) = N_Defining_Program_Unit_Name then
         N := Parent (N);
      end if;

      --  If the Parent pointer of E is not a subprogram specification node
      --  (going through an intermediate N_Defining_Program_Unit_Name node
      --  for subprogram units), then E is an inherited operation. Its parent
      --  points to the type derivation that produces the inheritance: that's
      --  the node that generates the subprogram specification. Its alias
      --  is the parent subprogram, and that one points to a subprogram
      --  declaration, or to another type declaration if this is a hierarchy
      --  of derivations.

      if Nkind (N) not in N_Subprogram_Specification then
         pragma Assert (Present (Alias (E)));
         N := Get_Subprogram_Spec (Alias (E));
      end if;

      return N;
   end Get_Subprogram_Spec;

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
            Contracts :=
              Find_Contracts (E, Name, Inherited => True);
         end if;
      else
         Contracts := Find_Contracts (E, Name);
      end if;

      return not Contracts.Is_Empty;
   end Has_Contracts;

   --------------------------------
   -- Has_Default_Init_Condition --
   --------------------------------

   function Has_Default_Init_Condition (E : Entity_Id) return Boolean is
      Base : constant Entity_Id :=
        (if Ekind (E) in Subtype_Kind then Etype (E) else E);
   begin
      if Is_Private_Type (Base) then
         return Has_Default_Init_Cond (Base)
           or else Has_Inherited_Default_Init_Cond (Base);
      else
         return False;
      end if;
   end Has_Default_Init_Condition;

   -----------------------------------
   -- Has_Extensions_Visible_Aspect --
   -----------------------------------

   function Has_Extensions_Visible_Aspect (E : Entity_Id) return Boolean
   is
   begin
      return Present (Get_Pragma (E, Pragma_Extensions_Visible));
   end Has_Extensions_Visible_Aspect;

   -------------------
   -- Has_No_Output --
   -------------------

   function Has_No_Output
     (E          : Entity_Id;
      GG_Allowed : Boolean) return Boolean
   is
      Params : constant List_Id :=
                 Parameter_Specifications (Get_Subprogram_Spec (E));
      Param  : Node_Id;

      Read_Ids    : Flow_Types.Flow_Id_Sets.Set;
      Write_Ids   : Flow_Types.Flow_Id_Sets.Set;
      Write_Names : Name_Set.Set;

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

      --  Consider output globals

      if GG_Allowed or else Has_User_Supplied_Globals (E) then
         Flow_Utility.Get_Proof_Globals (Subprogram => E,
                                         Classwide  => True,
                                         Reads      => Read_Ids,
                                         Writes     => Write_Ids);
         Write_Names := Flow_Types.To_Name_Set (Write_Ids);

         if not Write_Names.Is_Empty then
            return False;
         end if;
      end if;

      --  No output found

      return True;
   end Has_No_Output;

   ----------------------------------
   -- Has_Private_Ancestor_Or_Root --
   ----------------------------------

   function Has_Private_Ancestor_Or_Root (E : Entity_Id) return Boolean is
   begin
      if not Is_Tagged_Type (E) then
         return False;
      end if;

      if Has_Private_Ancestor (E) then
         return True;
      end if;

      declare
         Root : constant Entity_Id := Root_Record_Type (E);
      begin
         return E /= Root and then Fullview_Not_In_SPARK (Root);
      end;
   end Has_Private_Ancestor_Or_Root;

   -----------------------------------
   -- Has_Static_Discrete_Predicate --
   -----------------------------------

   function Has_Static_Discrete_Predicate (E : Entity_Id) return Boolean is
   begin
      return
        Is_Discrete_Type (E)
        and then Has_Predicates (E)
        and then Present (Static_Discrete_Predicate (E));
   end Has_Static_Discrete_Predicate;

   -------------------------------
   -- Has_Static_Scalar_Subtype --
   -------------------------------

   --  This function is similar to Sem_Eval.Is_Static_Subtype, except it only
   --  considers scalar subtypes (otherwise returns False), and looks part
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

   -------------------------
   -- Has_User_Defined_Eq --
   -------------------------

   function Has_User_Defined_Eq (E : Entity_Id) return Entity_Id is
      Prim : Elmt_Id;
      Op   : Entity_Id;
   begin

      Prim := First_Elmt (Collect_Primitive_Operations (E));
      while Present (Prim) loop
         Op := Node (Prim);

         if Chars (Op) = Name_Op_Eq
           and then Etype (Op) = Standard_Boolean
           and then Etype (First_Formal (Op)) = E
           and then Etype (Next_Formal (First_Formal (Op))) = E
         then
            return Op;
         end if;

         Next_Elmt (Prim);
      end loop;

      return Empty;
   end Has_User_Defined_Eq;

   -------------------------------
   -- Has_User_Supplied_Globals --
   -------------------------------

   function Has_User_Supplied_Globals (E : Entity_Id) return Boolean
   is (Present (Get_Pragma (E, Pragma_Global)) or else
         Present (Get_Pragma (E, Pragma_Depends)));

   ------------------
   -- Has_Volatile --
   ------------------

   function Has_Volatile (E : Entity_Id) return Boolean is
   begin
      case Ekind (E) is
         when E_Abstract_State =>
            return Is_External_State (E);
         when others =>
            return Is_Effectively_Volatile (E);
      end case;
   end Has_Volatile;

   -------------------------
   -- Has_Volatile_Aspect --
   -------------------------

   function Has_Volatile_Aspect (E : Entity_Id;
                                 A : Pragma_Id)
                                 return Boolean
   is
      function Has_Specific_Aspect (E : Entity_Id;
                                    A : Pragma_Id)
                                    return Boolean
      is (case A is
            when Pragma_Async_Readers =>
               Async_Readers_Enabled (E),
            when Pragma_Async_Writers =>
               Async_Writers_Enabled (E),
            when Pragma_Effective_Reads =>
               Effective_Reads_Enabled (E),
            when Pragma_Effective_Writes =>
               Effective_Writes_Enabled (E),
            when others =>
               raise Why.Unexpected_Node);
   begin
      case Ekind (E) is
         when E_Abstract_State =>
            case A is
               when Pragma_Async_Writers =>
                  return Async_Writers_Enabled (E);
               when Pragma_Effective_Reads =>
                  return Effective_Reads_Enabled (E);
               when Pragma_Async_Readers =>
                  return Async_Readers_Enabled (E);
               when Pragma_Effective_Writes =>
                  return Effective_Writes_Enabled (E);
               when others =>
                  raise Program_Error;
            end case;

         when E_In_Parameter =>
            case A is
               when Pragma_Async_Writers =>
                  return True;
               when Pragma_Async_Readers    |
                    Pragma_Effective_Reads  |
                    Pragma_Effective_Writes =>
                  return False;
               when others =>
                  raise Program_Error;
            end case;

         when E_Out_Parameter =>
            case A is
               when Pragma_Async_Writers | Pragma_Effective_Reads =>
                  return False;
               when Pragma_Async_Readers | Pragma_Effective_Writes =>
                  return True;
               when others =>
                  raise Program_Error;
            end case;

         when E_In_Out_Parameter =>
            return True;

         when E_Variable =>
            return Has_Specific_Aspect (E, A);

         when E_Constant =>
            --  SRM 7.1.3(6): A constant, a discriminant or a loop
            --  parameter shall not be Volatile.
            return False;

         when others =>
            Print_Tree_Node (E);
            raise Why.Unexpected_Node;
      end case;
   end Has_Volatile_Aspect;

   -----------------------
   -- In_Main_Unit_Body --
   -----------------------

   function In_Main_Unit_Body (N : Node_Id) return Boolean is
      CU   : constant Node_Id := Enclosing_Comp_Unit_Node (N);
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

         --  The only way a node in a subunit can be seen is when this subunit
         --  is part of the main unit.

         when N_Subunit =>
            return True;

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
      CU   : constant Node_Id := Enclosing_Comp_Unit_Node (N);
      Root : Node_Id;

   begin
      if No (CU) then
         return False;
      end if;

      Root := Unit (CU);

      case Nkind (Root) is
         when N_Package_Body    |
              N_Subprogram_Body |
              N_Subunit         =>

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

   ------------------------------
   -- Innermost_Enclosing_Loop --
   ------------------------------

   function Innermost_Enclosing_Loop (N : Node_Id) return Node_Id is
   begin
      return Get_Enclosing (N, N_Loop_Statement);
   end Innermost_Enclosing_Loop;

   -----------------------------------------------
   -- Is_Access_To_External_Axioms_Discriminant --
   -----------------------------------------------

   function Is_Access_To_External_Axioms_Discriminant (N : Node_Id)
                                                       return Boolean
   is
      E : constant Entity_Id := Entity (Selector_Name (N));
   begin
      return Ekind (E) = E_Discriminant
        and then Is_External_Axioms_Discriminant (E);
   end Is_Access_To_External_Axioms_Discriminant;

   -------------------------
   -- Is_Declared_In_Unit --
   -------------------------

   function Is_Declared_In_Unit (E : Entity_Id; Scope : Entity_Id)
                                 return Boolean is
   begin
      --  Parameters of subprograms cannot be local to a unit.

      return Get_Enclosing_Unit (E) = Scope
        and then not (Ekind (E) in E_In_Parameter
                          | E_In_Out_Parameter | E_Out_Parameter);
   end Is_Declared_In_Unit;

   ---------------------------------------------
   -- Is_Double_Precision_Floating_Point_Type --
   ---------------------------------------------

   function Is_Double_Precision_Floating_Point_Type
     (E : Entity_Id) return Boolean is
   begin
      return Is_Floating_Point_Type (E)
        and then Machine_Radix_Value (E) = Uint_2
        and then Machine_Mantissa_Value (E) = UI_From_Int (53)
        and then Machine_Emax_Value (E) = Uint_2 ** Uint_10
        and then Machine_Emin_Value (E) = Uint_3 - (Uint_2 ** Uint_10);
   end Is_Double_Precision_Floating_Point_Type;

   -------------------------------------
   -- Is_External_Axioms_Discriminant --
   -------------------------------------

   function Is_External_Axioms_Discriminant (E : Entity_Id) return Boolean is
      Typ : constant Entity_Id :=
        Unique_Defining_Entity (Get_Enclosing_Declaration (E));
   begin
      return Type_Based_On_External_Axioms (Etype (Typ));
   end Is_External_Axioms_Discriminant;

   ------------------
   -- Is_Full_View --
   ------------------

   function Is_Full_View (E : Entity_Id) return Boolean is
      (Full_To_Partial_Entities.Contains (E));

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

   function Is_In_Analyzed_Files (E : Entity_Id) return Boolean
   is
      Encl_Unit : Node_Id := Enclosing_Comp_Unit_Node (E);
   begin

      --  Encl_Unit is supposed to be the node of the unit which contains
      --  E. But the call to Enclosing_Comp_Unit_Node may return the subunit
      --  instead of the compilation unit. We rectify this now:

      if Nkind (Unit (Encl_Unit)) = N_Subunit then
         Encl_Unit := Library_Unit (Encl_Unit);
      end if;

      --  if the entity is not in the
      --  compilation unit that is currently being analyzed then return false.

      if Cunit (Main_Unit) /= Encl_Unit
        and then Library_Unit (Cunit (Main_Unit)) /= Encl_Unit
      then
         return False;
      end if;

      --  If option -u was not present, or an empty files list has been
      --  provided then all entities that are in the compilation unit that
      --  is currently being analyzed must be analyzed.

      if not Gnat2Why_Args.Single_File or else
        Gnat2Why_Args.Analyze_File.Is_Empty
      then
         return True;
      end if;

      declare
         Spec_Prefix : constant String := Spec_File_Name (E);
         Body_Prefix : constant String := Body_File_Name (E);
      begin
         for A_File of Gnat2Why_Args.Analyze_File loop
            declare
               Filename : constant String := File_Name (A_File);
            begin
               if Equal_Case_Insensitive (Filename, Body_Prefix)
                 or else Equal_Case_Insensitive (Filename, Spec_Prefix)
               then
                  return True;
               end if;
            end;
         end loop;
         return False;
      end;
   end Is_In_Analyzed_Files;

   ------------------------
   -- Is_In_Current_Unit --
   ------------------------

   function Is_In_Current_Unit (N : Node_Id) return Boolean is
      Real_Node : constant Node_Id :=
        (if Is_Itype (N) then Associated_Node_For_Itype (N) else N);
   begin

      --  ??? Should be made more efficient

      return In_Main_Unit_Spec (Real_Node) or else
        In_Main_Unit_Body (Real_Node);
   end Is_In_Current_Unit;

   ----------------------------------------
   -- Is_Local_Subprogram_Always_Inlined --
   ----------------------------------------

   function Is_Local_Subprogram_Always_Inlined
     (E : Entity_Id) return Boolean is
   begin
      --  A subprogram always inlined should have Body_To_Inline set and flag
      --  Is_Inlined_Always set to True.

      return Ekind_In (E, E_Function, E_Procedure)
        and then Present (Get_Subprogram_Decl (E))
        and then Present (Body_To_Inline (Get_Subprogram_Decl (E)))
        and then Is_Inlined_Always (E);
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
   begin
      if not Is_Discrete_Type (T)
        or else not Has_Static_Scalar_Subtype (T)
      then
         return False;
      end if;
      declare
         Rng : constant Node_Id := Scalar_Range (T);
      begin
         return (Expr_Value (Low_Bound (Rng)) > Expr_Value (High_Bound (Rng)));
      end;
   end Is_Null_Range;

   ----------------------
   -- Is_Others_Choice --
   ----------------------

   function Is_Others_Choice (Choices : List_Id) return Boolean is
   begin
      return List_Length (Choices) = 1
        and then Nkind (First (Choices)) = N_Others_Choice;
   end Is_Others_Choice;

   ------------------------------
   -- Is_Overriding_Subprogram --
   ------------------------------

   function Is_Overriding_Subprogram (E : Entity_Id) return Boolean is
      Inherited : constant Subprogram_List := Inherited_Subprograms (E);
   begin
      return Inherited'Length > 0;
   end Is_Overriding_Subprogram;

   ----------------------
   -- Is_Package_State --
   ----------------------

   function Is_Package_State (E : Entity_Id) return Boolean is
   begin
      case Ekind (E) is
         when E_Abstract_State =>
            return True;

         when E_Variable =>
            case Ekind (Scope (E)) is
               when E_Package =>
                  return True;

               when others =>
                  return False;
            end case;

         when others =>
            return False;
      end case;
   end Is_Package_State;

   ---------------------
   -- Is_Partial_View --
   ---------------------

   function Is_Partial_View (E : Entity_Id) return Boolean is
      (Present (Full_View (E)));

   ---------------
   -- Is_Pragma --
   ---------------

   function Is_Pragma (N : Node_Id; Name : Pragma_Id) return Boolean is
     (Nkind (N) = N_Pragma
       and then Get_Pragma_Id (Pragma_Name (N)) = Name);

   ----------------------------------
   -- Is_Pragma_Annotate_Gnatprove --
   ----------------------------------

   function Is_Pragma_Annotate_Gnatprove (N : Node_Id) return Boolean is
     (Is_Pragma (N, Pragma_Annotate)
        and then
      Get_Name_String
        (Chars (Get_Pragma_Arg (First (Pragma_Argument_Associations (N)))))
      = "gnatprove");

   ------------------------------
   -- Is_Pragma_Assert_And_Cut --
   ------------------------------

   function Is_Pragma_Assert_And_Cut (N : Node_Id) return Boolean
   is
      Orig : constant Node_Id := Original_Node (N);
   begin
      return
        (Present (Orig) and then
         Nkind (Orig) = N_Pragma and then
         Get_Name_String (Chars (Pragma_Identifier (Orig))) =
           "assert_and_cut");
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
   begin
      return
        (Present (Scope (E)) and then
         Present (Parent (Scope (E))) and then
         Nkind (Parent (Scope (E))) = N_Quantified_Expression);
   end Is_Quantified_Loop_Param;

   -----------------------------
   -- Is_Requested_Subprogram --
   -----------------------------

   function Is_Requested_Subprogram (E : Entity_Id) return Boolean is
   begin
      return Ekind (E) in Subprogram_Kind
               and then
             "GP_Subp:" & To_String (Gnat2Why_Args.Limit_Subp) =
             SPARK_Util.Subp_Location (E);
   end Is_Requested_Subprogram;

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

   ---------------------------------------------
   -- Is_Single_Precision_Floating_Point_Type --
   ---------------------------------------------

   function Is_Single_Precision_Floating_Point_Type
     (E : Entity_Id) return Boolean is
   begin
      return Is_Floating_Point_Type (E)
        and then Machine_Radix_Value (E) = Uint_2
        and then Machine_Mantissa_Value (E) = Uint_24
        and then Machine_Emax_Value (E) = Uint_2 ** Uint_7
        and then Machine_Emin_Value (E) = Uint_3 - (Uint_2 ** Uint_7);
   end Is_Single_Precision_Floating_Point_Type;

   -------------------------------
   -- Is_Spec_Unit_Of_Main_Unit --
   -------------------------------

   function Is_Spec_Unit_Of_Main_Unit (N : Node_Id) return Boolean is
     (Present (Corresponding_Body (N))
       and then Is_Main_Cunit
        (Unit (Enclosing_Comp_Unit_Node (Corresponding_Body (N)))));

   ------------------------------
   -- Is_Standard_Boolean_Type --
   ------------------------------

   function Is_Standard_Boolean_Type (N : Node_Id) return Boolean is
   begin
      return N = Standard_Boolean or else
        (Nkind (N) in N_Entity and then
         Ekind (N) = E_Enumeration_Subtype and then
         Etype (N) = Standard_Boolean and then
         Scalar_Range (N) = Scalar_Range (Etype (N)));
   end Is_Standard_Boolean_Type;

   ------------------------
   -- Is_Toplevel_Entity --
   ------------------------

   function Is_Toplevel_Entity (E : Entity_Id) return Boolean is
      P : Entity_Id;

   begin
      P := Scope (E);

      --  Itypes and class-wide types may not have a declaration, or a
      --  declaration which is not inserted in the AST. Do not consider these
      --  as toplevel entities.

      if Is_Itype (E) or else Ekind (E) = E_Class_Wide_Type then
         return False;
      end if;

      while Present (P) loop
         if Ekind (P) not in E_Generic_Package |
                             E_Package         |
                             E_Package_Body
         then
            return False;
         end if;

         P := Scope (P);
      end loop;

      return True;
   end Is_Toplevel_Entity;

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
      Cur_Formal : Node_Id := First_Entity (Entity (Name (Call)));
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

   --------------------------------
   -- Lexicographic_Entity_Order --
   --------------------------------

   function Lexicographic_Entity_Order
     (Left, Right : Node_Id) return Boolean is
   begin
      return Unique_Name (Left) < Unique_Name (Right);
   end Lexicographic_Entity_Order;

   ----------------------------------
   -- Location_In_Standard_Library --
   ----------------------------------

   function Location_In_Standard_Library (Loc : Source_Ptr) return Boolean is
   begin
      if Loc = No_Location then
         return False;
      end if;

      if Loc = Standard_Location
        or else Loc = Standard_ASCII_Location
        or else Loc = System_Location
      then
         return True;
      end if;

      return Unit_In_Standard_Library (Unit (Get_Source_File_Index (Loc)));
   end Location_In_Standard_Library;

   -----------------------------
   -- Lowercase_Capacity_Name --
   -----------------------------

   function Lowercase_Capacity_Name return String is ("capacity");

   --------------------------------
   -- Lowercase_Has_Element_Name --
   --------------------------------

   function Lowercase_Has_Element_Name return String is ("has_element");

   ----------------------------
   -- Lowercase_Iterate_Name --
   ----------------------------

   function Lowercase_Iterate_Name return String is ("iterate");

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

   -------------------
   -- Might_Be_Main --
   -------------------

   function Might_Be_Main (E : Entity_Id) return Boolean is
   begin
      return (Scope_Depth_Value (E) = Uint_1 or else
                (Is_Generic_Instance (E) and then
                   Scope_Depth_Value (E) = Uint_2))
        and then No (First_Formal (E));
   end Might_Be_Main;

   ---------
   -- MUT --
   ---------

   function MUT (T : Entity_Id) return Entity_Id is
      Typ : Entity_Id := T;
   begin
      loop
         --  For types whose ultimate fullview is not in SPARK, fullviews are
         --  not translated.

         if not Entity_In_SPARK (Typ) or else Fullview_Not_In_SPARK (Typ) then

            if Is_Full_View (Typ) then
               Typ := Partial_View (Typ);
            end if;

            return Typ;
         elsif Ekind (Typ) in Private_Kind then
            Typ := Underlying_Type (Typ);
         else
            return Typ;
         end if;
      end loop;
   end MUT;

   --------------
   -- MUT_Kind --
   --------------

   function MUT_Kind (T : Entity_Id) return Entity_Kind is
      Typ : Entity_Id := T;
   begin
      loop
         if Ekind (Typ) in Private_Kind then
            Typ := Underlying_Type (Typ);
         else
            exit;
         end if;
      end loop;

      return Ekind (Typ);
   end MUT_Kind;

   --------------------
   -- Nth_Index_Type --
   --------------------

   function Nth_Index_Type (E : Entity_Id; Dim : Uint) return Node_Id
   is
      Cur   : Int := 1;
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

   function Nth_Index_Type (E : Entity_Id; Dim : Positive) return Node_Id
   is
   begin
      return Nth_Index_Type (E, UI_From_Int (Int (Dim)));
   end Nth_Index_Type;

   -----------------------
   -- Number_Components --
   -----------------------

   function Number_Components (Typ : Entity_Id) return Natural is
      Count     : Natural := 0;
      Component : Entity_Id := First_Component_Or_Discriminant (Typ);
   begin
      while Present (Component) loop

         --  Do not count completely hidden discrimiants

         if not (Ekind (Component) = E_Discriminant
                 and then Is_Completely_Hidden (Component))
         then
            Count := Count + 1;
         end if;
         Component := Next_Component_Or_Discriminant (Component);
      end loop;
      return Count;
   end Number_Components;

   --------------------------
   -- Number_Discriminants --
   --------------------------

   function Number_Discriminants (Typ : Entity_Id) return Natural is
      Count     : Natural := 0;
      Component : Entity_Id := First_Discriminant (Typ);
   begin
      while Present (Component) loop

         --  Do not count completely hidden discrimiants

         if not (Ekind (Component) = E_Discriminant
                 and then Is_Completely_Hidden (Component))
         then
            Count := Count + 1;
         end if;
         Component := Next_Discriminant (Component);
      end loop;
      return Count;
   end Number_Discriminants;

   ---------------------------------
   -- Package_Has_External_Axioms --
   ---------------------------------

   function Package_Has_External_Axioms (E : Entity_Id) return Boolean
   is
   begin
      return Has_Annotate_Pragma_For_External_Axiomatization (E);
   end Package_Has_External_Axioms;

   ------------------
   -- Partial_View --
   ------------------

   function Partial_View (E : Entity_Id) return Entity_Id is
      (Full_To_Partial_Entities.Element (E));

   ---------------------------
   -- Root_Record_Component --
   ---------------------------

   function Root_Record_Component (E : Entity_Id) return Entity_Id is
      Rec_Type : constant Entity_Id := MUT (Scope (E));
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
                  Cur_Type := Unique_Entity (Etype (Cur_Type));
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
      Ancestor : Entity_Id := E;
   begin
      --  Climb the type derivation chain with Root_Type, applying
      --  Underlying_Type or Get_First_Ancestor_In_SPARK to pass private type
      --  boundaries.

      while Ancestor /= Result loop
         pragma Assert (Entity_In_SPARK (Ancestor));

         Result := Ancestor;
         Ancestor := Root_Type (Result);

         if not Entity_In_SPARK (Ancestor) then
            pragma Assert (Fullview_Not_In_SPARK (Result));
            Ancestor := Result;
         end if;

         if Fullview_Not_In_SPARK (Ancestor) then
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
        (if Is_Class_Wide_Type (Rec) then
              Get_Specific_Type_From_Classwide (Rec)
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
      --  Returns the uncapitalized unqualified name for entity E

      ----------------
      -- Short_Name --
      ----------------

      function Short_Name (E : Entity_Id) return String is
      begin
         Get_Unqualified_Name_String (Chars (E));
         return Name_Buffer (1 .. Name_Len);
      end Short_Name;

      Name : String := Short_Name (E);
      Loc  : Source_Ptr := Sloc (E);
      Buf  : Source_Buffer_Ptr;

   --  Start of Source_Name

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
   end Source_Name;

   --------------------
   -- Spec_File_Name --
   --------------------

   function Spec_File_Name (N : Node_Id) return String
   is
      CU : Node_Id := Enclosing_Comp_Unit_Node (N);
   begin
      case Nkind (Unit (CU)) is
         when N_Package_Body | N_Subunit =>
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
      if Ekind (F_Index) = E_String_Literal_Subtype then
         return String_Literal_Length (F_Index);
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

   function String_Of_Node (N : Node_Id) return String
   is

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

   begin
      return Node_To_String (N, "");
   end String_Of_Node;

   -------------------
   -- Subp_Location --
   -------------------

   function Subp_Location (E : Entity_Id) return String
   is
      S : constant Subp_Type := Entity_To_Subp (E);
      B : constant Base_Sloc := Subp_Sloc (S).First_Element;
   begin

      --  ??? Probably need to change this code to take M412-032 into account

      return
        "GP_Subp:" & Base_Sloc_File (B) & ":" & Image (B.Line, 1);
   end Subp_Location;

   ---------------------------------
   -- Subprogram_Full_Source_Name --
   ---------------------------------

   function Subprogram_Full_Source_Name (E : Entity_Id) return String
   is
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

   function Subprogram_Is_Ignored_For_Proof (E : Entity_Id) return Boolean is
     (Is_Predicate_Function (E) or else Is_Invariant_Procedure (E)
          or else Is_Default_Init_Cond_Procedure (E));

   -----------------------------------
   -- Type_Based_On_External_Axioms --
   -----------------------------------

   function Type_Based_On_External_Axioms (E : Entity_Id) return Boolean is
     (Present (Underlying_External_Axioms_Type (E)));

   -------------------------------------
   -- Underlying_External_Axioms_Type --
   -------------------------------------

   function Underlying_External_Axioms_Type (E : Entity_Id) return Entity_Id
   is
      Typ : Entity_Id := Etype (E);
   begin
      loop

         --  Go through Etype to the most underlying private declaration
         while Etype (Typ) /= Typ and Ekind (Typ) in Private_Kind loop
            Typ := Etype (Typ);
         end loop;

         if Ekind (Typ) in Private_Kind and then
           Entity_In_External_Axioms (Typ)
         then
            return Typ;
         else
            return Empty;
         end if;
      end loop;
   end Underlying_External_Axioms_Type;

end SPARK_Util;
