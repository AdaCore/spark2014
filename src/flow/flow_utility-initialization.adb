------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--          F L O W _ U T I L I T Y . I N I T I A L I Z A T I O N           --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                Copyright (C) 2014-2020, Altran UK Limited                --
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

with Aspects;                    use Aspects;
with Namet;                      use Namet;
with Nlists;                     use Nlists;
with SPARK_Util.External_Axioms; use SPARK_Util.External_Axioms;
with Sem_Type;                   use Sem_Type;

package body Flow_Utility.Initialization is

   ----------------------------
   -- Default_Initialization --
   ----------------------------

   function Default_Initialization (Typ        : Entity_Id;
                                    Ignore_DIC : Boolean := False)
                                    return Default_Initialization_Kind
   is
      FDI : Boolean := False;
      NDI : Boolean := False;
      --  Two flags used to designate whether a record type has at least one
      --  fully default initialized component and/or one not fully default
      --  initialized component.

      procedure Process_Component (Comp : Entity_Id)
      with Pre  => Ekind (Comp) = E_Component,
           Post => (if FDI'Old then FDI) and then (if NDI'Old then NDI);
      --  Process component of a record or of a record extension

      -----------------------
      -- Process_Component --
      -----------------------

      procedure Process_Component (Comp : Entity_Id) is
         ORC : constant Entity_Id := Original_Record_Component (Comp);
         --  The components of discriminated subtypes are not marked as source
         --  entities because they are technically "inherited" on the spot. To
         --  handle such components, use the original record component defined
         --  in the parent type.

         Init : Default_Initialization_Kind;

      begin
         --  Do not process internally generated components except for _parent
         --  which represents the ancestor portion of a derived type.

         if Comes_From_Source (ORC)
           or else Chars (ORC) = Name_uParent
         then
            --  When the component has a default expression, then it is default
            --  initialized no matter of its type.

            if Present (Expression (Parent (ORC))) then
               FDI := True;
               return;
            end if;

            --  If a component is not visible in SPARK, we assume it to be not
            --  initialized.

            Init :=
              (if Component_Is_Visible_In_SPARK (ORC)
               then Default_Initialization (Base_Type (Etype (ORC)),
                                            Ignore_DIC)
               else No_Default_Initialization);

            --  Default initialization of the record depends then on the
            --  default initialization of the component type.

            case Init is
               --  Mixed initialization renders the entire record mixed

               when Mixed_Initialization =>
                  FDI := True;
                  NDI := True;

               --  The component is fully default initialized when its type is
               --  fully default initialized.

               when Full_Default_Initialization =>
                  FDI := True;

               --  Components with no possible initialization are ignored

               when No_Possible_Initialization =>
                  null;

               --  The component has no full default initialization

               when No_Default_Initialization =>
                  NDI := True;
            end case;
         end if;
      end Process_Component;

      --  Local variables

      Comp   : Entity_Id;
      Result : Default_Initialization_Kind;

   --  Start of processing for Default_Initialization

   begin
      --  For types that are not in SPARK we trust the declaration. This means
      --  that if we find a Default_Initial_Condition aspect we trust it.

      if Ignore_DIC
        and then Full_View_Not_In_SPARK (Typ)
      then
         return Default_Initialization (Typ);
      end if;

      --  If we are considering implicit initializations and
      --  Default_Initial_Condition was specified for the type, take it into
      --  account.

      if not Ignore_DIC
        and then Has_Own_DIC (Typ)
      then
         declare
            Prag : constant Node_Id :=
              Get_Pragma (Typ, Pragma_Default_Initial_Condition);

         begin
            --  The pragma has an argument. If NULL, this indicates a value of
            --  the type is not default initialized. Otherwise, a value of the
            --  type should be fully default initialized.

            if Present (Prag) then
               declare
                  Pragma_Assoc : constant List_Id :=
                    Pragma_Argument_Associations (Prag);

               begin
                  if Present (Pragma_Assoc)
                    and then Nkind (Get_Pragma_Arg (First (Pragma_Assoc))) =
                               N_Null
                  then
                     Result := No_Default_Initialization;
                  else
                     Result := Full_Default_Initialization;
                  end if;
               end;

            --  Otherwise the pragma appears without an argument, indicating a
            --  value of the type if fully default initialized.

            else
               Result := Full_Default_Initialization;
            end if;
         end;

      --   We assume access types to be initialized to null

      elsif Is_Access_Type (Typ) then
         Result := Full_Default_Initialization;

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
         pragma Assert (Entity_In_SPARK (Base_Type (Typ)));
         Result := Default_Initialization (Base_Type (Typ),
                                           Ignore_DIC);

      --  A derived type is only initialized if its base type and any
      --  extensions that it defines are fully default initialized.

      elsif Is_Derived_Type (Typ) then
         --  If the type does inherit a default initial condition then we take
         --  it into account.

         if not Ignore_DIC
           and then Has_Inherited_DIC (Typ)
         then
            pragma Assert (Entity_In_SPARK (Etype (Typ)));
            Result := Default_Initialization (Etype (Typ),
                                              Ignore_DIC);
         else
            declare
               Type_Def : Node_Id;
               Rec_Part : Node_Id := Empty;

               Parent_Typ : constant Node_Id := Parent (Typ);

            begin
               --  If Typ is an Itype, it may not have an Parent field pointing
               --  to a corresponding declaration. In that case, there is no
               --  record extension part to check for default initialization.

               --  If the corresponding declaration is a full type declaration
               --  for a derived type definition or a type declaration with a
               --  private extension, then there is an extension part to check.
               --  ??? a type with a private extension should kind of be
               --  handled by like a private type.

               if Present (Parent_Typ) then
                  case Nkind (Parent_Typ) is
                     when N_Full_Type_Declaration =>
                        Type_Def := Type_Definition (Parent_Typ);

                        if Nkind (Type_Def) = N_Derived_Type_Definition then
                           Rec_Part := Record_Extension_Part (Type_Def);
                        end if;

                     when N_Private_Extension_Declaration =>
                        if Full_View_Not_In_SPARK (Typ) then
                           null;
                        else
                           Type_Def :=
                             Type_Definition
                               (Original_Node (Parent (Full_View (Typ))));
                           --  The Original_Node above is needed because
                           --  frontend rewrites:
                           --
                           --    type T is new R (...) [with ...];
                           --
                           --  into:
                           --
                           --    type BT is new R [with ...];
                           --    subtype T is BT (...);
                           --
                           --  see Build_Derived_Record_Type, step 5.

                           if Nkind (Type_Def) = N_Derived_Type_Definition then
                              Rec_Part := Record_Extension_Part (Type_Def);
                           end if;
                        end if;

                     when others =>
                        null;
                  end case;
               else
                  pragma Assert (Is_Itype (Typ));
               end if;

               --  If there is an extension part then we need to look into it
               --  in order to determine initialization of the type.

               if Present (Rec_Part) then

                  pragma Assert (Is_Tagged_Type (Typ));

                  --  If the extension is null then initialization of this type
                  --  is equivalent to the initialization for its Etype.

                  if Null_Present (Rec_Part) then
                     pragma Assert (Entity_In_SPARK (Etype (Typ)));
                     Result := Default_Initialization (Etype (Typ),
                                                       Ignore_DIC);

                     --  If the extension is not null then we need to analyse
                     --  it.

                  else
                     --  When the derived type has extensions we check both
                     --  the base type and the extensions.
                     declare
                        Base_Initialized : Default_Initialization_Kind;
                        Ext_Initialized  : Default_Initialization_Kind;

                     begin
                        pragma Assert (Entity_In_SPARK (Etype (Typ)));
                        Base_Initialized :=
                          Default_Initialization (Etype (Typ),
                                                  Ignore_DIC);

                        Comp :=
                          First_Non_Pragma
                            (Component_Items (Component_List (Rec_Part)));

                        --  Inspect all components of the extension

                        if Present (Comp) then
                           while Present (Comp) loop
                              Process_Component (Defining_Identifier (Comp));
                              Next_Non_Pragma (Comp);
                           end loop;

                           --  Detect a mixed case of initialization

                           if FDI and NDI then
                              Ext_Initialized := Mixed_Initialization;

                           elsif FDI then
                              Ext_Initialized :=
                                Full_Default_Initialization;

                           elsif NDI then
                              Ext_Initialized := No_Default_Initialization;

                           --  The type either has no components or they are
                           --  all internally generated. The extensions are
                           --  trivially fully default initialized

                           else
                              Ext_Initialized :=
                                Full_Default_Initialization;
                           end if;

                        --  The extension is null, there is nothing to
                        --  initialize.

                        else
                           if Ignore_DIC then
                              --  The extensions are trivially fully default
                              --  initialized.
                              Ext_Initialized :=
                                Full_Default_Initialization;
                           else
                              Ext_Initialized :=
                                No_Possible_Initialization;
                           end if;
                        end if;

                        if Base_Initialized = Full_Default_Initialization
                          and then Ext_Initialized =
                          Full_Default_Initialization
                        then
                           Result := Full_Default_Initialization;
                        else
                           Result := No_Default_Initialization;
                        end if;
                     end;
                  end if;

               --  If there is no extension then we analyse initialization for
               --  the Etype.

               else
                  pragma Assert (Entity_In_SPARK (Etype (Typ)));
                  Result := Default_Initialization (Etype (Typ),
                                                    Ignore_DIC);
               end if;
            end;
         end if;

      --  The initialization status of a private type depends on its full view

      elsif Is_Private_Type (Typ) then
         declare
            Full_V : constant Entity_Id :=
              (if Present (Full_View (Typ))
               then Full_View (Typ)
               elsif Present (Underlying_Full_View (Typ))
               then Underlying_Full_View (Typ)
               else Etype (Typ));
            --  Typicall we expect the full view to be present, but for example
            --  on derived types without additional constraints it is not. This
            --  code is inspired by Einfo.Underlying_Type and should be robust.

            pragma Assert (Is_Type (Full_V) and then Full_V /= Typ);

         begin
            --  If the full view is not visible from the Scope then we can
            --  consider the type to be fully initialized if it has a DIC.

            if Full_View_Not_In_SPARK (Typ) then

               Result :=
                 (if Has_Own_DIC (Typ)
                  then Full_Default_Initialization
                  else No_Default_Initialization);

            --  Continue analysing the full view of the private type only if it
            --  is visible from the Scope and its full view is in SPARK.

            else
               pragma Assert (Entity_In_SPARK (Full_V));

               Result := Default_Initialization (Full_V, Ignore_DIC);
            end if;
         end;

      --  Concurrent types are always fully default initialized

      elsif Is_Concurrent_Type (Typ) then
         Result := Full_Default_Initialization;

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
                                              Ignore_DIC);
         end if;

      --  Record types and protected types offer several initialization options
      --  depending on their components (if any).

      elsif Is_Record_Type (Typ) then
         Comp := First_Component (Typ);

         --  Inspect all components

         if Present (Comp) then
            while Present (Comp) loop
               Process_Component (Comp);
               Next_Component (Comp);
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
               if Ignore_DIC then
                  --  The record is considered to be trivially fully
                  --  default initialized.
                  Result := Full_Default_Initialization;
               else
                  Result := No_Possible_Initialization;
               end if;
            end if;

         --  The type is null, there is nothing to initialize.

         else
            if Ignore_DIC then
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

   --------------------------------
   -- Get_Default_Initialization --
   --------------------------------

   function Get_Default_Initialization (F : Flow_Id) return Node_Id is
      function Get_Component_From_Aggregate
        (A : Node_Id;
         C : Entity_Id)
         return Node_Id
      with
        Pre =>
          Nkind (A) = N_Aggregate
            and then
          Ekind (C) in E_Component | E_Discriminant,
        Post =>
          (if Present (Get_Component_From_Aggregate'Result)
           then Nkind (Get_Component_From_Aggregate'Result) in N_Subexpr);
      --  If we have a record aggregate A like (X => Y, Z => W), this returns
      --  the value attached to component C, for example if C is Z this will
      --  return W.

      function Get_Simple_Default (E : Entity_Id) return Node_Id
      with Pre  => Is_Type (E),
           Post => (if Present (Get_Simple_Default'Result)
                    then Nkind (Get_Simple_Default'Result) in N_Subexpr);
      --  Recursively look for simple default values given by Default_Value and
      --  Default_Component_Value.

      ----------------------------------
      -- Get_Component_From_Aggregate --
      ----------------------------------

      function Get_Component_From_Aggregate
        (A : Node_Id;
         C : Entity_Id)
         return Node_Id
      is
         N : Node_Id := First (Component_Associations (A));
      begin
         while Present (N) loop
            if Entity (First (Choices (N))) = C then
               return Expression (N);
            end if;

            Next (N);
         end loop;

         --  So, we can't find the component we're looking for; this means
         --  we have some kind of discriminated type with a variant part;
         --  and we statically know some part is not present. We return
         --  Empty in this case to gracefully handle it (as flow analyis
         --  always initializes 'all' components on aggregate assignments).
         return Empty;
      end Get_Component_From_Aggregate;

      ------------------------
      -- Get_Simple_Default --
      ------------------------

      function Get_Simple_Default (E : Entity_Id) return Node_Id is
      begin
         if Has_Aspect (E, Aspect_Default_Value) then
            return Expression (Find_Aspect (E, Aspect_Default_Value));
         elsif Has_Aspect (E, Aspect_Default_Component_Value) then
            return Expression
              (Find_Aspect (E, Aspect_Default_Component_Value));
         else
            case Ekind (E) is
               when E_Array_Subtype =>
                  return Get_Simple_Default (Etype (E));

               when E_Array_Type =>
                  return Get_Simple_Default (Component_Type (E));

               when others =>
                  return Empty;
            end case;
         end if;
      end Get_Simple_Default;

      N       : Node_Id;
      Comp_Id : Positive;

   --  Start of processing for Get_Default_Initialization

   begin
      case F.Kind is
         when Direct_Mapping =>
            return Get_Simple_Default (Etype (Get_Direct_Mapping_Id (F)));

         when Record_Field =>
            --  If the Flow_Id represents the 'Hidden part of a record then we
            --  do not consider it to be initialized.
            if Is_Private_Part (F)
              or else Is_Extension (F)
              or else Is_Record_Tag (F)
            then
               return Empty;
            end if;

            --  We need to find the first one with a default initialization as
            --  that would overwrite any default initialization we might find
            --  later.
            Comp_Id := 1;
            for Comp of F.Component loop
               N := Expression (Parent (Comp));
               if Present (N) then
                  --  This is a field with a default initalization

                  --  We can try and untangle any record aggregates
                  while Comp_Id < Positive (F.Component.Length)
                    and then Nkind (N) = N_Aggregate
                  loop
                     Comp_Id := Comp_Id + 1;
                     N := Get_Component_From_Aggregate
                       (N,
                        F.Component (Comp_Id));
                  end loop;

                  return N;
               end if;

               Comp_Id := Comp_Id + 1;
            end loop;

            --  We need to check if the type itself is always initialized
            return Get_Simple_Default (Etype (F.Component.Last_Element));

         when Magic_String
            | Synthetic_Null_Export
            | Null_Value
         =>
            raise Program_Error;
      end case;
   end Get_Default_Initialization;

   ----------------------------
   -- Is_Default_Initialized --
   ----------------------------

   function Is_Default_Initialized
     (F          : Flow_Id;
      Ignore_DIC : Boolean := False)
      return Boolean
   is

      function Has_Full_Default_Initialization (E : Entity_Id) return Boolean;
      --  Returns True iff F has full default initialization

      -------------------------------------
      -- Has_Full_Default_Initialization --
      -------------------------------------

      function Has_Full_Default_Initialization (E : Entity_Id) return Boolean
      is
         Typ : Entity_Id;
      begin
         case Ekind (E) is
            when E_Abstract_State =>
               return False;

            when Type_Kind =>
               Typ := E;

            when others =>
               Typ := Etype (E);
         end case;

         return Default_Initialization (Typ, Ignore_DIC) =
                  Full_Default_Initialization;
      end Has_Full_Default_Initialization;

   --  Start of processing for Is_Default_Initialized

   begin
      case F.Kind is
         when Direct_Mapping =>
            declare
               E : constant Entity_Id := Get_Direct_Mapping_Id (F);

            begin
               return Is_Imported (E)
                 or else In_Generic_Actual (E)
                 or else Has_Full_Default_Initialization (E);
            end;

         when Record_Field =>
            if In_Generic_Actual (Get_Direct_Mapping_Id (F))
              or else Is_Imported (Get_Direct_Mapping_Id (F))
            then
               return True;
            end if;

            if Is_Discriminant (F) then
               return Present (Discriminant_Default_Value
                                 (F.Component.Last_Element));

            elsif Is_Record_Tag (F) then
               return True;

            else
               --  For nested records with mixed default-initialization we
               --  first look at the most nested component and then at its
               --  parents until the very top-level object.

               return
                 (for some Comp of reverse F.Component =>
                    (Has_Full_Default_Initialization (Comp)
                     or else Present (Expression (Parent (Comp)))))
                   or else
                 Has_Full_Default_Initialization (Get_Direct_Mapping_Id (F));
            end if;

         when Magic_String
            | Null_Value
            | Synthetic_Null_Export
         =>
            raise Program_Error;
      end case;
   end Is_Default_Initialized;

end Flow_Utility.Initialization;
