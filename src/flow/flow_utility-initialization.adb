------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--          F L O W _ U T I L I T Y . I N I T I A L I Z A T I O N           --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--              Copyright (C) 2014-2025, Capgemini Engineering              --
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

with Aspects;     use Aspects;
with Nlists;      use Nlists;
with Opt;         use Opt;
with Sem_Prag;    use Sem_Prag;
with Sem_Type;    use Sem_Type;
with Sinfo.Utils; use Sinfo.Utils;
with Sinput;      use Sinput;

package body Flow_Utility.Initialization is

   ----------------------------
   -- Default_Initialization --
   ----------------------------

   function Default_Initialization
     (Typ : Entity_Id; Ignore_DIC : Boolean := False)
      return Default_Initialization_Kind
   is
      FDI : Boolean := False;
      NDI : Boolean := False;
      --  Two flags used to designate whether a record type has at least one
      --  fully default initialized component and/or one not fully default
      --  initialized component.

      procedure Process_Component (Comp : Entity_Id)
      with
        Pre  => Ekind (Comp) = E_Component,
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
         --  Don't expect internally generated components

         pragma
           Assert
             (Comes_From_Source (ORC)
                or else Comes_From_Inlined_Body (Sloc (ORC)));

         --  When the component has a default expression, then it is default
         --  initialized no matter of its type.

         if Present (Expression (Parent (ORC))) then
            FDI := True;
            return;
         end if;

         Init := Default_Initialization (Etype (ORC));

         --  Default initialization of the record depends then on the default
         --  initialization of the component type.

         case Init is
            --  Mixed initialization renders the entire record mixed

            when Mixed_Initialization        =>
               FDI := True;
               NDI := True;

            --  The component is fully default initialized when its type is
            --  fully default initialized.

            when Full_Default_Initialization =>
               FDI := True;

            --  Components with no possible initialization are ignored

            when No_Possible_Initialization  =>
               null;

            --  The component has no full default initialization

            when No_Default_Initialization   =>
               NDI := True;
         end case;
      end Process_Component;

      --  Local variables

      Decl   : Node_Id;
      Def    : Node_Id;
      Result : Default_Initialization_Kind;

      --  Start of processing for Default_Initialization

   begin
      --  If we are considering implicit initializations and explicit
      --  Default_Initial_Condition was specified for the type, take it into
      --  account.

      if not Ignore_DIC and then Has_Own_DIC (Typ) then
         declare
            --  For types with DIC, given either by an aspect or a pragma,
            --  frontend rewrites them into:
            --
            --     pragma Default_Initial_Condition
            --       ([null | boolean_expression], type_name);

            Prag : constant Node_Id :=
              Get_Pragma (Typ, Pragma_Default_Initial_Condition);

            pragma Assert (Present (Prag));

            Assocs : constant List_Id := Pragma_Argument_Associations (Prag);

            pragma Assert (List_Length (Assocs) = 2);

            Arg1 : constant Node_Id := Get_Pragma_Arg (First (Assocs));

         begin
            --  If NULL, this indicates a value of the type is not default
            --  initialized. Otherwise, a value of the type should be fully
            --  default initialized.

            if Nkind (Arg1) = N_Null then
               return No_Default_Initialization;
            else
               return Full_Default_Initialization;
            end if;
         end;
      end if;

      --  Types in the Standard package lack declarations that we could
      --  process, so conservatively (yet quite rightly) consider them
      --  as uninitialized by default.

      if Sloc (Typ) = Standard_Location then
         return No_Default_Initialization;
      end if;

      --  ??? Previously class-wide types reported no possible initialization,
      --  because their First_Component/Next_Component chain was empty; let's
      --  keep this behaviour for a moment.

      if Is_Class_Wide_Type (Typ) then
         return No_Possible_Initialization;
      end if;

      --  If type is explicitly annotated with SPARK_Mode => Off, we assume
      --  it to be uninitialized by default and stop the traversal.

      if Present (SPARK_Pragma (Typ))
        and then Get_SPARK_Mode_From_Annotation (SPARK_Pragma (Typ)) = Opt.Off
      then
         return No_Default_Initialization;
      end if;

      --  We attempt to process type declaration as it occurs in source code

      Decl := Parent (Typ);

      --  If we find that the above declaration is incomplete, as it typically
      --  happens for itypes, we will jump at the corresponding original source
      --  code declaration.

      <<LOOK_AT_SOURCE_DECLARATION>>

      case Nkind (Decl) is
         when N_Full_Type_Declaration                                =>

            Def := Type_Definition (Decl);

            case Nkind (Def) is

               --  Access types are initialized by default

               when N_Access_To_Object_Definition
                  | N_Access_Function_Definition
                  | N_Access_Procedure_Definition    =>
                  return Full_Default_Initialization;

               --  Array types might have aspect Default_Component_Value or
               --  their components might be initialized by default.

               when N_Array_Type_Definition          =>
                  if Has_Default_Aspect (Typ) then
                     return Full_Default_Initialization;
                  else
                     return
                       Default_Initialization (Component_Type (Typ), False);
                  end if;

               --  Derived types might inherit the Default_Value and
               --  Default_Component_Value aspect (for scalar and array
               --  types, respectively); otherwise, we examine the parent
               --  type and any added components.

               when N_Derived_Type_Definition        =>
                  if Has_Default_Aspect (Typ) then
                     return Full_Default_Initialization;
                  end if;

                  declare
                     Parent_Initialization : Default_Initialization_Kind;

                     S_Indication : constant Node_Id :=
                       Subtype_Indication (Def);

                     Record_Extension : constant Node_Id :=
                       Record_Extension_Part (Def);

                     CList : Node_Id;
                     CItem : Node_Id;

                  begin
                     if Is_Entity_Name (S_Indication) then
                        Parent_Initialization :=
                          Default_Initialization (Entity (S_Indication));
                     elsif Nkind (S_Indication) = N_Subtype_Indication then
                        Parent_Initialization :=
                          Default_Initialization
                            (Entity (Subtype_Mark (S_Indication)));
                     else
                        raise Program_Error;
                     end if;

                     if Present (Record_Extension) then
                        pragma
                          Assert
                            (Present (Component_List (Record_Extension))
                               xor Null_Present (Record_Extension));

                        if Null_Present (Record_Extension) then
                           null;
                        else
                           CList := Component_List (Record_Extension);

                           CItem := First_Non_Pragma (Component_Items (CList));
                           while Present (CItem) loop
                              Process_Component (Defining_Identifier (CItem));
                              --  Optimization: exit when already decided
                              if FDI and NDI then
                                 return Mixed_Initialization;
                              end if;
                              Next_Non_Pragma (CItem);
                           end loop;

                           pragma Assert (No (Variant_Part (CList)));
                        end if;
                     end if;

                     if FDI and NDI then
                        Result := Mixed_Initialization;

                     elsif FDI then
                        Result := Parent_Initialization;

                     elsif NDI then
                        if Parent_Initialization
                           in No_Default_Initialization
                            | No_Possible_Initialization
                        then
                           Result := No_Default_Initialization;
                        else
                           --  ??? Previosly a fully initialized parent
                           --  extended with a non-initialized component
                           --  resulted in No_Default_Initialization, though
                           --  intuitively it should have Mixed_Initialization.

                           Result := No_Default_Initialization;
                        end if;
                     else
                        Result := Parent_Initialization;
                     end if;

                     return Result;
                  end;

               --  Scalar types either have Default_Value aspect or are
               --  uninitialized.

               when N_Enumeration_Type_Definition
                  | N_Modular_Type_Definition
                  | N_Floating_Point_Definition
                  | N_Decimal_Fixed_Point_Definition
                  | N_Ordinary_Fixed_Point_Definition
                  | N_Signed_Integer_Type_Definition =>
                  if Has_Default_Aspect (Typ) then
                     return Full_Default_Initialization;
                  else
                     return No_Default_Initialization;
                  end if;

               --  For record types we traverse their component declarations

               when N_Record_Definition              =>
                  declare
                     CList   : Node_Id := Component_List (Def);
                     CItem   : Node_Id;
                     VPart   : Node_Id;
                     Variant : Node_Id;
                  begin
                     pragma Assert (Present (CList) xor Null_Present (Def));

                     if Present (CList) then
                        CItem := First_Non_Pragma (Component_Items (CList));
                        while Present (CItem) loop
                           Process_Component (Defining_Identifier (CItem));
                           --  Optimization: exit when already decided
                           if FDI and NDI then
                              return Mixed_Initialization;
                           end if;
                           Next_Non_Pragma (CItem);
                        end loop;

                        VPart := Variant_Part (CList);
                        if Present (VPart) then
                           Variant := First_Non_Pragma (Variants (VPart));
                           while Present (Variant) loop
                              CList := Component_List (Variant);
                              CItem :=
                                First_Non_Pragma (Component_Items (CList));
                              while Present (CItem) loop
                                 Process_Component
                                   (Defining_Identifier (CItem));
                                 --  Optimization: exit when already decided
                                 if FDI and NDI then
                                    return Mixed_Initialization;
                                 end if;
                                 Next_Non_Pragma (CItem);
                              end loop;
                              Next_Non_Pragma (Variant);
                           end loop;
                        end if;
                     end if;

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

                     return Result;
                  end;

               when others                           =>
                  raise Program_Error;
            end case;

         --  For private types created by the frontend, e.g. for derived
         --  private types, we jump to their original source code declarations.

         when N_Private_Type_Declaration                             =>
            if not Comes_From_Source (Decl)
              and then Comes_From_Source (Original_Node (Decl))
            then
               Decl := Original_Node (Decl);
               goto LOOK_AT_SOURCE_DECLARATION;
            end if;

            --  Otherwise, look at the full view

            Result := Default_Initialization (Full_View (Typ));

            --  In specific cases, we'd rather consider the type as
            --  having no default initialization (which is allowed in
            --  SPARK) rather than mixed initialization (which is not
            --  allowed).

            if Result = Mixed_Initialization then
               return No_Default_Initialization;
            else
               return Result;
            end if;

         --  For private extension respect their SPARK_Mode barrier, if present

         when N_Private_Extension_Declaration                        =>

            --  If the SPARK_Mode barrier is Off, then combine initialization
            --  status of the parent with the assumed uninitilised status of
            --  the private part.

            if Present (SPARK_Pragma (Full_View (Typ)))
              and then
                Get_SPARK_Mode_From_Annotation (SPARK_Pragma (Full_View (Typ)))
                = Opt.Off
            then
               declare
                  S_Indication          : constant Node_Id :=
                    Subtype_Indication (Decl);
                  Parent_Initialization : Default_Initialization_Kind;
               begin
                  if Is_Entity_Name (S_Indication) then
                     Parent_Initialization :=
                       Default_Initialization (Entity (S_Indication));
                  elsif Nkind (S_Indication) = N_Subtype_Indication then
                     Parent_Initialization :=
                       Default_Initialization
                         (Entity (Subtype_Mark (S_Indication)));
                  else
                     raise Program_Error;
                  end if;

                  case Parent_Initialization is
                     when No_Possible_Initialization
                        | No_Default_Initialization                          =>
                        return No_Default_Initialization;

                     when Full_Default_Initialization | Mixed_Initialization =>
                        return Mixed_Initialization;
                  end case;
               end;

            --  Otherwise recurse into full type declaration

            else
               return Default_Initialization (Full_View (Typ));
            end if;

         --  Subtype declarations, just like private types, might be
         --  inserted by the frontend, so we look at the original source
         --  code declarations.

         when N_Subtype_Declaration                                  =>
            if not Comes_From_Source (Decl)
              and then Comes_From_Source (Original_Node (Decl))
            then
               Decl := Original_Node (Decl);
               goto LOOK_AT_SOURCE_DECLARATION;
            end if;

            declare
               S_Indication : constant Node_Id := Subtype_Indication (Decl);
            begin
               if Is_Entity_Name (S_Indication) then
                  return Default_Initialization (Entity (S_Indication));
               elsif Nkind (S_Indication) = N_Subtype_Indication then
                  return
                    Default_Initialization
                      (Entity (Subtype_Mark (S_Indication)));
               else
                  raise Program_Error;
               end if;
            end;

         --  Concurrent types, looking from the outside, are initialized by
         --  default.

         when N_Protected_Type_Declaration | N_Task_Type_Declaration =>
            return Full_Default_Initialization;

         --  Recurse into itypes created by component declarations

         when N_Component_Declaration                                =>

            pragma Assert (Is_Itype (Typ));

            declare
               C_Def        : constant Node_Id := Component_Definition (Decl);
               S_Indication : constant Node_Id := Subtype_Indication (C_Def);
               A_Definition : constant Node_Id := Access_Definition (C_Def);
            begin
               pragma
                 Assert (Present (S_Indication) xor Present (A_Definition));

               if Present (S_Indication) then
                  --  Itypes are only atteached to those component declarations
                  --  that declare constrained subtypes; otherwise, the type
                  --  indicated by entity name is used directly.

                  pragma Assert (Nkind (S_Indication) = N_Subtype_Indication);

                  return
                    Default_Initialization
                      (Entity (Subtype_Mark (S_Indication)));
               else
                  pragma
                    Annotate
                      (Xcov,
                       Exempt_On,
                       "Anonymous access types are rejected in marking");
                  return Full_Default_Initialization;
                  pragma Annotate (Xcov, Exempt_Off);
               end if;
            end;

         --  Other itypes have either no parent at all or the parent has no
         --  semantic significance.

         when others                                                 =>
            pragma Assert (Is_Itype (Typ));

            --  We recurse into the underlying type, except for types, where
            --  it could be an infinite recursion. Instead for those we do the
            --  same analysis as for fully declared types.

            if Is_Access_Type (Typ) then
               return Full_Default_Initialization;

            elsif Is_Array_Type (Typ) then
               if Has_Default_Aspect (Typ) then
                  return Full_Default_Initialization;
               else
                  return Default_Initialization (Component_Type (Typ));
               end if;

            elsif Is_Scalar_Type (Typ) then
               if Has_Default_Aspect (Typ) then
                  return Full_Default_Initialization;
               else
                  return No_Default_Initialization;
               end if;

            else
               pragma Assert (Etype (Typ) /= Typ);
               return Default_Initialization (Etype (Typ));
            end if;

      end case;
   end Default_Initialization;

   --------------------------------
   -- Get_Default_Initialization --
   --------------------------------

   function Get_Default_Initialization (F : Flow_Id) return Node_Id is
      function Get_Component_From_Aggregate
        (A : Node_Id; C : Entity_Id) return Node_Id
      with
        Pre  =>
          Nkind (A) = N_Aggregate
          and then Ekind (C) in E_Component | E_Discriminant,
        Post =>
          (if Present (Get_Component_From_Aggregate'Result)
           then Nkind (Get_Component_From_Aggregate'Result) in N_Subexpr);
      --  If we have a record aggregate A like (X => Y, Z => W), this returns
      --  the value attached to component C, for example if C is Z this will
      --  return W.

      function Get_Simple_Default (E : Entity_Id) return Node_Id
      with
        Pre  => Is_Type (E),
        Post =>
          (if Present (Get_Simple_Default'Result)
           then Nkind (Get_Simple_Default'Result) in N_Subexpr);
      --  Recursively look for simple default values given by Default_Value and
      --  Default_Component_Value.

      ----------------------------------
      -- Get_Component_From_Aggregate --
      ----------------------------------

      function Get_Component_From_Aggregate
        (A : Node_Id; C : Entity_Id) return Node_Id
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
            return
              Expression (Find_Aspect (E, Aspect_Default_Component_Value));
         else
            case Ekind (E) is
               when E_Array_Subtype =>
                  return Get_Simple_Default (Etype (E));

               when E_Array_Type    =>
                  return Get_Simple_Default (Component_Type (E));

               when others          =>
                  return Empty;
            end case;
         end if;
      end Get_Simple_Default;

      N       : Node_Id;
      Comp_Id : Positive;

      --  Start of processing for Get_Default_Initialization

   begin
      case F.Kind is
         when Direct_Mapping                                    =>
            return Get_Simple_Default (Etype (Get_Direct_Mapping_Id (F)));

         when Record_Field                                      =>
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
                     N :=
                       Get_Component_From_Aggregate (N, F.Component (Comp_Id));
                  end loop;

                  return N;
               end if;

               Comp_Id := Comp_Id + 1;
            end loop;

            --  We need to check if the type itself is always initialized
            return Get_Simple_Default (Etype (F.Component.Last_Element));

         when Magic_String | Synthetic_Null_Export | Null_Value =>
            raise Program_Error;
      end case;
   end Get_Default_Initialization;

   ----------------------------
   -- Is_Default_Initialized --
   ----------------------------

   function Is_Default_Initialized
     (F : Flow_Id; Ignore_DIC : Boolean := False) return Boolean
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

            when Type_Kind        =>
               Typ := E;

            when others           =>
               Typ := Etype (E);
         end case;

         return
           Default_Initialization (Typ, Ignore_DIC)
           = Full_Default_Initialization;
      end Has_Full_Default_Initialization;

      --  Start of processing for Is_Default_Initialized

   begin
      case F.Kind is
         when Direct_Mapping                                    =>
            declare
               E : constant Entity_Id := Get_Direct_Mapping_Id (F);

            begin
               return
                 Is_Imported (E)
                 or else In_Generic_Actual (E)
                 or else Has_Full_Default_Initialization (E);
            end;

         when Record_Field                                      =>
            if In_Generic_Actual (Get_Direct_Mapping_Id (F))
              or else Is_Imported (Get_Direct_Mapping_Id (F))
            then
               return True;
            end if;

            if Is_Discriminant (F) then
               return
                 Present
                   (Discriminant_Default_Value (F.Component.Last_Element));

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

         when Magic_String | Null_Value | Synthetic_Null_Export =>
            raise Program_Error;
      end case;
   end Is_Default_Initialized;

end Flow_Utility.Initialization;
