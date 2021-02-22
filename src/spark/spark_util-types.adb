------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                        S P A R K _ U T I L - T Y P E S                   --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                     Copyright (C) 2016-2021, AdaCore                     --
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

with Aspects;                    use Aspects;
with Elists;                     use Elists;
with Sem_Eval;                   use Sem_Eval;
with Sinfo.Utils;                use Sinfo.Utils;
with SPARK_Definition;           use SPARK_Definition;
with SPARK_Util.Subprograms;     use SPARK_Util.Subprograms;

package body SPARK_Util.Types is

   function Type_Name_For_Explanation (Typ : Entity_Id) return String
     is (if not Is_Itype (Typ) then "type " & Source_Name (Typ)
         else "anonymous type")
     with Pre => Is_Type (Typ);
   --  This function computes a user-visible string to represent the type in
   --  argument.

   generic
      with procedure Callback
        (Typ         : Entity_Id;
         Result      : out Boolean;
         Explanation : out Unbounded_String);
   procedure Check_Composite_Types_For_Holes
     (Typ         : Entity_Id;
      Size        : Uint;
      Result      : out Boolean;
      Explanation : out Unbounded_String);
   --  This function is used by Type_Has_No_Holes and
   --  Is_Valid_Bitpattern_No_Holes to recurse over composite types. It checks
   --  that the composite types have no holes, and that each field has the
   --  property checked by the Callback.

   ---------------------------------------------
   -- Queries related to representative types --
   ---------------------------------------------

   function Base_Retysp (T : Entity_Id) return Entity_Id is
      E : Entity_Id := Retysp (T);
   begin
      while not Is_Base_Type (E) loop
         E := Retysp (Base_Type (E));
      end loop;
      return E;
   end Base_Retysp;

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
               goto Returning;

            --  No partial view in SPARK, return T

            elsif not Entity_Marked (Typ)
              or else not Is_Full_View (Typ)
            then
               Typ := T;
               goto Returning;

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
                  goto Returning;
               end if;

            --  If we have a private type with an underlying full view, either
            --  it is in SPARK and we reach it, or it is not in SPARK and we
            --  return at this point.

            elsif Is_Private_Type (Typ)
              and then Present (Underlying_Full_View (Typ))
            then
               if Entity_In_SPARK (Underlying_Full_View (Typ)) then
                  Typ := Underlying_Full_View (Typ);
                  pragma Assert (Full_View_Not_In_SPARK (Typ));
               else
                  goto Returning;
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
                  goto Returning;
               end if;

            --  Derived types without additional constraints might not have
            --  Full_View defined; search the on the Etype instead.

            elsif Is_Private_Type (Typ) then
               pragma Assert (Etype (Typ) /= Typ);
               if Entity_In_SPARK (Etype (Typ)) then
                  Typ := Etype (Typ);
                  pragma Assert (Full_View_Not_In_SPARK (Typ));
               else
                  goto Returning;
               end if;
            else
               goto Returning;
            end if;
         end loop;

      --  Otherwise, Typ's most underlying type is in SPARK, return it.

      else
         pragma Assert (Entity_In_SPARK (Unchecked_Full_Type (Typ)));
         Typ := Unchecked_Full_Type (Typ);
      end if;

      <<Returning>>

      --  Do not return the subtype introduced for a formal type in a generic
      --  instantiation, if we can return the actual itself. We recognize here
      --  cases where the formal in the instance is defined as a simple subtype
      --  of the actual:
      --
      --    subtype Formal is Actual;
      --
      --  It is important to skip the intermediate subtype generated by the
      --  frontend, in the case where this type is used as the designated type
      --  of some access types, because the frontend then generates an AST with
      --  conversions between access types that would not be allowed in source
      --  code, because the designated types are not exactly the same (they are
      --  similar subtypes of the same base type). And our translation to Why3
      --  depends on being able to unify all such access types.

      if Entity_In_SPARK (Typ) and then Is_Generic_Actual_Type (Typ) then
         declare
            Decl    : constant Node_Id := Parent (Typ);
            Sub_Ind : Node_Id;
         begin
            if Present (Decl)
              and then Nkind (Decl) = N_Subtype_Declaration
            then
               Sub_Ind := Subtype_Indication (Decl);
               if Nkind (Sub_Ind) in N_Has_Entity
                 and then Present (Entity (Sub_Ind))
               then
                  Typ := Retysp (Entity (Sub_Ind));
               end if;
            end if;
         end;
      end if;

      return Typ;

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

   begin
      return Has_Invariants_In_SPARK (Ty)
        and then Is_Declared_In_Main_Unit_Or_Parent (Real_Node);
   end Has_Visible_Type_Invariants;

   ------------------------------------
   -- Has_Unconstrained_UU_Component --
   ------------------------------------

   function Has_Unconstrained_UU_Component (Typ : Entity_Id) return Boolean is
      Rep_Ty : constant Entity_Id := Root_Retysp (Typ);
      --  For tagged types, go to the root type. UU_Components cannot be
      --  contained in derivations, as this would be rejected in marking.

   begin
      if Is_Record_Type (Rep_Ty) then
         declare
            Comp : Node_Id := First_Component (Rep_Ty);
         begin
            while Present (Comp) loop
               if Component_Is_Visible_In_SPARK (Comp) then
                  return (Is_Unchecked_Union (Retysp (Etype (Comp)))
                          and then not Is_Constrained (Retysp (Etype (Comp))))
                    or else Has_Unconstrained_UU_Component (Etype (Comp));
               end if;
               Next_Component (Comp);
            end loop;
         end;
         return False;
      elsif Is_Array_Type (Rep_Ty) then
         return (Is_Unchecked_Union (Retysp (Component_Type (Rep_Ty)))
                 and then
                   not Is_Constrained (Retysp (Component_Type (Rep_Ty))))
           or else Has_Unconstrained_UU_Component (Component_Type (Rep_Ty));
      else
         return False;
      end if;
   end Has_Unconstrained_UU_Component;

   -------------------------------------
   -- Check_Composite_Types_For_Holes --
   -------------------------------------

   procedure Check_Composite_Types_For_Holes
     (Typ         : Entity_Id;
      Size        : Uint;
      Result      : out Boolean;
      Explanation : out Unbounded_String)
   is
   begin
      if Is_Array_Type (Typ) then
         if not Is_Static_Array_Type (Typ) then
            Result := False;
            Explanation :=
              To_Unbounded_String ("size of non-static array type cannot "
                                   & "be determined");
            return;
         end if;

         declare
            Comp_Typ : constant Entity_Id :=
              Retysp (Component_Type (Typ));
            Mult_Size : Uint := Uint_1;
            Index : Entity_Id;
         begin
            Callback (Comp_Typ, Result, Explanation);
            if not Result then
               return;
            end if;

            pragma Assert (Known_RM_Size (Comp_Typ));

            Mult_Size := UI_Mul (Mult_Size, RM_Size (Comp_Typ));
            Index := First_Index (Typ);
            while Present (Index) loop
               declare
                  Rng : constant Node_Id := Get_Range (Index);
               begin
                  Mult_Size :=
                    UI_Mul (Mult_Size,
                            UI_Add (
                              UI_Sub (Expr_Value (High_Bound (Rng)),
                                Expr_Value (Low_Bound (Rng))),
                              Uint_1));
                  Next_Index (Index);
               end;
            end loop;
            if not UI_Eq (Size, Mult_Size) then
               Result := False;
               Explanation :=
                 To_Unbounded_String
                   ("array type has size " & UI_Image (Size) & " but "
                    & "components add up to size " & UI_Image (Mult_Size));
               return;
            end if;
         end;

      end if;

      if Is_Record_Type (Typ) then
         declare
            Comp     : Node_Id := First_Component (Typ);
            Sum_Size : Uint := Uint_0;
         begin
            while Present (Comp) loop
               declare
                  Comp_Ty  : constant Entity_Id := Retysp (Etype (Comp));
               begin
                  if Ekind (Comp) = E_Component then
                     Callback
                       (Comp_Ty, Result, Explanation);
                     if not Result then
                        return;
                     end if;
                  end if;
                  pragma Assert (Known_RM_Size (Comp_Ty));
                  Sum_Size := UI_Add (Sum_Size, RM_Size (Comp_Ty));
                  Next_Component (Comp);
               end;
            end loop;
            if not UI_Eq (Size, Sum_Size) then
               Result := False;
               Explanation :=
                 To_Unbounded_String
                   ("record type has size " & UI_Image (Size) & " but "
                    & "components add up to size " & UI_Image (Sum_Size));
               return;
            end if;
         end;
      end if;
      Result := True;
      Explanation := To_Unbounded_String ("");
      return;
   end Check_Composite_Types_For_Holes;

   ------------------------------
   -- Check_DIC_At_Declaration --
   ------------------------------

   function Check_DIC_At_Declaration (E : Entity_Id) return Boolean is
      Default_Init_Subp : constant Entity_Id := Partial_DIC_Procedure (E);
      Default_Init_Expr : constant Node_Id :=
        Get_Expr_From_Check_Only_Proc (Default_Init_Subp);
      Init_Param        : constant Entity_Id :=
        First_Formal (Default_Init_Subp);

      function Is_Ref_Through_Discr (N : Node_Id) return Boolean with
        Pre => Nkind (N) in N_Identifier | N_Expanded_Name;
      --  Return True if N is the prefix of a discriminant

      function Is_Type_Instance (N : Node_Id) return Traverse_Result;
      --  Traverse N searching for references to the current type instance. The
      --  traversal stops with Abandon if and only if such a reference is
      --  found. References through discriminants do not count.

      --------------------------
      -- Is_Ref_Through_Discr --
      --------------------------

      function Is_Ref_Through_Discr (N : Node_Id) return Boolean is
         P : constant Node_Id := Parent (N);

      begin
         --  We should only be called on a node with a Parent

         pragma Assert (Present (P));

         --  For selected components, traversal should only consider the
         --  prefix.

         pragma Assert
           (if Nkind (P) = N_Selected_Component then Prefix (P) = N);

         return Nkind (P) = N_Selected_Component
           and then Ekind (Entity (Selector_Name (P))) = E_Discriminant;
      end Is_Ref_Through_Discr;

      ----------------------
      -- Is_Type_Instance --
      ----------------------

      function Is_Type_Instance (N : Node_Id) return Traverse_Result is
      begin
         case Nkind (N) is
            when N_Identifier | N_Expanded_Name =>
               if Entity (N) = Init_Param
                 and then not Is_Ref_Through_Discr (N)
               then
                  return Abandon;
               else
                  return Skip;
               end if;
            when others =>
               null;
         end case;
         return OK;
      end Is_Type_Instance;

      function Refers_To_Type_Instance is new Traverse_More_Func
        (Process => Is_Type_Instance);

   begin
      return Refers_To_Type_Instance (Default_Init_Expr) = Abandon;
   end Check_DIC_At_Declaration;

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

      elsif To_R = Retysp (Etype (From_R)) then
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

   ---------------------------------
   -- Contains_Relaxed_Init_Parts --
   ---------------------------------

   function Contains_Relaxed_Init_Parts
     (Typ        : Entity_Id;
      Ignore_Top : Boolean := False) return Boolean
   is
      Rep_Ty : constant Entity_Id := Retysp (Typ);
   begin
      if not Ignore_Top and then Has_Relaxed_Init (Typ) then
         return True;

      --  Concurrent or access types with relaxed init parts are not supported

      elsif Ekind (Rep_Ty) in Concurrent_Kind | Access_Kind then
         return False;

      elsif Is_Array_Type (Rep_Ty) then
         return Contains_Relaxed_Init_Parts (Component_Type (Rep_Ty));

      elsif Is_Record_Type (Rep_Ty) then

         --  Tagged types with relaxed init parts are not supported

         if Is_Tagged_Type (Rep_Ty) then
            return False;
         else
            declare
               Comp : Entity_Id := First_Component (Rep_Ty);
            begin
               while Present (Comp) loop
                  if Component_Is_Visible_In_SPARK (Comp)
                    and then Contains_Relaxed_Init_Parts (Etype (Comp))
                  then
                     return True;
                  end if;
                  Next_Component (Comp);
               end loop;
            end;
         end if;
         return False;
      else
         pragma Assert
           (Is_Private_Type (Rep_Ty) or else Is_Scalar_Type (Rep_Ty));
         return False;
      end if;
   end Contains_Relaxed_Init_Parts;

   --------------------------------
   -- Contains_Only_Relaxed_Init --
   --------------------------------

   function Contains_Only_Relaxed_Init (Typ : Entity_Id) return Boolean is
      Rep_Ty : constant Entity_Id := Retysp (Typ);
   begin
      if Has_Relaxed_Init (Typ) then
         return True;

      --  Concurrent or access types with relaxed init parts are not supported

      elsif Is_Concurrent_Type (Rep_Ty) or else Is_Access_Type (Rep_Ty) then
         return False;

      elsif Is_Array_Type (Rep_Ty) then
         return Contains_Only_Relaxed_Init (Component_Type (Rep_Ty));

      elsif Is_Record_Type (Rep_Ty) then

         --  Tagged types with relaxed init parts are not supported

         if Is_Tagged_Type (Rep_Ty) then
            return False;

         --  Return True if Rep_Ty contains at least a subcomponent with
         --  relaxed initialization and only such components.

         else
            declare
               Comp             : Entity_Id := First_Component (Rep_Ty);
               Has_Visible_Comp : Boolean := False;
            begin
               while Present (Comp) loop
                  if Component_Is_Visible_In_SPARK (Comp) then

                     --  We have found at least one component with relaxed
                     --  init. If we don't find any component without it, then
                     --  the type contains only relaxed init parts.

                     if Contains_Only_Relaxed_Init (Etype (Comp)) then
                        Has_Visible_Comp := True;

                     --  We have found at least one component without relaxed
                     --  init. We return False directly.

                     else
                        return False;
                     end if;
                  end if;
                  Next_Component (Comp);
               end loop;

               --  The loop exits normally, so all components of Typ have
               --  relaxed init. We return True if it has at least one
               --  such components.

               return Has_Visible_Comp;
            end;
         end if;
      else
         pragma Assert
           (Is_Private_Type (Rep_Ty) or else Is_Scalar_Type (Rep_Ty));
         return False;
      end if;
   end Contains_Only_Relaxed_Init;

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

   -------------------------
   -- Find_Predicate_Item --
   -------------------------

   procedure Find_Predicate_Item (Ty : Entity_Id; Rep_Item : in out Node_Id) is
   begin
      while Present (Rep_Item) loop
         case Nkind (Rep_Item) is
            when N_Pragma =>

               --  Ignore pragmas coming from aspect specification. It will be
               --  analyzed when the corresponding aspect is found.

               if From_Aspect_Specification (Rep_Item) then
                  null;
               elsif Get_Pragma_Id (Pragma_Name (Rep_Item)) = Pragma_Predicate
                 and then Unique_Entity
                   (Entity
                      (Expression
                         (First (Pragma_Argument_Associations (Rep_Item))))) =
                   Unique_Entity (Ty)
               then
                  return;
               end if;
            when N_Aspect_Specification =>
               if Get_Aspect_Id (Rep_Item) in Aspect_Predicate
                                            | Aspect_Dynamic_Predicate
                                            | Aspect_Static_Predicate
                   and then Unique_Entity (Entity (Rep_Item)) =
                     Unique_Entity (Ty)
               then
                  return;
               end if;
            when others => null;
         end case;
         Next_Rep_Item (Rep_Item);
      end loop;
   end Find_Predicate_Item;

   -------------------------------------
   -- Get_Parent_Type_If_Check_Needed --
   -------------------------------------

   function Get_Parent_Type_If_Check_Needed (N : Node_Id) return Entity_Id is
   begin
      if Nkind (N) = N_Full_Type_Declaration then
         declare
            T_Def : constant Node_Id := Type_Definition (N);
         begin
            case Nkind (T_Def) is
               when N_Subtype_Indication =>
                  return Entity (Subtype_Mark (T_Def));

               when N_Derived_Type_Definition =>
                  declare
                     S : constant Node_Id := Subtype_Indication (T_Def);
                  begin
                     return Entity (if Nkind (S) = N_Subtype_Indication
                                    then Subtype_Mark (S)
                                    else S);
                  end;

               when others =>
                  return Empty;
            end case;
         end;
      else
         declare
            S : constant Node_Id := Subtype_Indication (N);
         begin
            return Entity (if Nkind (S) = N_Subtype_Indication
                           then Subtype_Mark (S)
                           else S);
         end;
      end if;
   end Get_Parent_Type_If_Check_Needed;

   --------------------------------------
   -- Get_Specific_Type_From_Classwide --
   --------------------------------------

   function Get_Specific_Type_From_Classwide (E : Entity_Id) return Entity_Id
   is
      Specific_Type : constant Entity_Id := Etype (Base_Type (E));

   begin
      if Is_Full_View (Specific_Type) then
         return Partial_View (Specific_Type);
      else
         return Specific_Type;
      end if;
   end Get_Specific_Type_From_Classwide;

   ----------------------------------
   -- Get_Access_Type_From_Profile --
   ----------------------------------

   function Get_Access_Type_From_Profile (Ty : Entity_Id) return Entity_Id is
     (Defining_Entity (Associated_Node_For_Itype (Ty)));

   ------------------------------
   -- Get_Constraint_For_Discr --
   ------------------------------

   function Get_Constraint_For_Discr
     (Ty    : Entity_Id;
      Discr : Entity_Id)
      return Node_Id
   is
      Current : Entity_Id := First_Discriminant (Ty);
      Elmt    : Elmt_Id := First_Elmt (Discriminant_Constraint (Ty));
   begin
      while Current /= Discr loop
         Next_Discriminant (Current);
         Next_Elmt (Elmt);
      end loop;
      return Node (Elmt);
   end Get_Constraint_For_Discr;

   -----------------------------
   -- Has_Invariants_In_SPARK --
   -----------------------------

   function Has_Invariants_In_SPARK (E : Entity_Id) return Boolean is
     (Has_Own_Invariants (E)
      and then Is_Base_Type (E)
      and then (if Is_Partial_View (E) then Entity_In_SPARK (Full_View (E))));

   ------------------------
   -- Has_Private_Fields --
   ------------------------

   function Has_Private_Fields (E : Entity_Id) return Boolean is
      Ty : constant Entity_Id := Retysp (E);
   begin
      if not Full_View_Not_In_SPARK (Ty) then
         return False;
      end if;

      --  Only base types have private fields of their own; subtypes do not

      if not Is_Base_Type (Ty) then
         return False;
      end if;

      --  Derived non-tagged types cannot have private fields of their own.

      if not Is_Tagged_Type (Ty)
        and then Retysp (Etype (Ty)) /= Ty
      then
         return False;
      end if;

      --  Return True if Ty is a private type

      return Is_Private_Type (Ty);
   end Has_Private_Fields;

   ----------------------------
   -- Invariant_Check_Needed --
   ----------------------------

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

         Parent := Retysp (Etype (Current));
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

         declare
            Comp : Node_Id := First_Component (Rep_Ty);
         begin
            while Present (Comp) loop
               if Ekind (Comp) = E_Component
                 and then Entity_In_SPARK (Etype (Comp))
                 and then Invariant_Check_Needed (Etype (Comp))
               then
                  return True;
               end if;
               Next_Component (Comp);
            end loop;
         end;
      end if;
      return False;
   end Invariant_Check_Needed;

   -------------
   -- Is_Deep --
   -------------

   function Is_Deep (Typ : Entity_Id) return Boolean is
      Rep_Typ : constant Entity_Id := Retysp (Typ);
   begin
      case Type_Kind'(Ekind (Rep_Typ)) is
         when Access_Kind =>

            --  Access to subprograms are not subjected to ownership rules

            return Ekind (Directly_Designated_Type (Rep_Typ)) /=
              E_Subprogram_Type;

         when E_Array_Type
            | E_Array_Subtype
         =>
            return Is_Deep (Component_Type (Rep_Typ));

         when Record_Kind =>
            declare
               Comp : Entity_Id := First_Component_Or_Discriminant (Rep_Typ);
            begin
               while Present (Comp) loop

                  --  Ignore components not visible in SPARK

                  if Component_Is_Visible_In_SPARK (Comp)
                    and then Is_Deep (Etype (Comp))
                  then
                     return True;
                  end if;
                  Next_Component_Or_Discriminant (Comp);
               end loop;
            end;
            return False;

         when Scalar_Kind
            | E_String_Literal_Subtype
            | Concurrent_Kind
            | Incomplete_Kind
            | E_Exception_Type
            | E_Subprogram_Type
         =>
            return False;

         --  Ignore full view of types if it is not in SPARK

         when E_Private_Type
            | E_Private_Subtype
            | E_Limited_Private_Type
            | E_Limited_Private_Subtype
         =>
            return False;
      end case;
   end Is_Deep;

   -------------------
   -- Is_Null_Range --
   -------------------

   function Is_Null_Range (T : Entity_Id) return Boolean is
     (Is_Discrete_Type (T)
      and then Has_Static_Scalar_Subtype (T)
      and then Expr_Value (Type_Low_Bound (T)) >
          Expr_Value (Type_High_Bound (T)));

   ----------------------
   -- Is_Standard_Type --
   ----------------------

   --  E might be a standard type or the implicit base type of such a standard
   --  type.
   function Is_Standard_Type (E : Entity_Id) return Boolean is
     (for some S_Type in S_Types =>
         E = Standard_Entity (S_Type) or E = Etype (Standard_Entity (S_Type)));

   ------------------------------
   -- Is_Standard_Boolean_Type --
   ------------------------------

   function Is_Standard_Boolean_Type (E : Entity_Id) return Boolean is
     ((E = Standard_Boolean
       or else
         (Ekind (E) = E_Enumeration_Subtype
          and then Etype (E) = Standard_Boolean
          and then Scalar_Range (E) = Scalar_Range (Standard_Boolean)
          and then not Has_Predicates (E)))
      and then not In_Relaxed_Init (E));

   --------------------------
   -- Is_Static_Array_Type --
   --------------------------

   function Is_Static_Array_Type (E : Entity_Id) return Boolean is
     (Is_Array_Type (E)
        and then Is_Constrained (E)
        and then Has_Static_Array_Bounds (E));

   -----------------------
   -- Type_Has_No_Holes --
   -----------------------

   procedure Type_Has_No_Holes (Typ         : Entity_Id;
                                Result      : out Boolean;
                                Explanation : out Unbounded_String)
   is

      procedure Type_Has_No_Holes_Internal
        (Typ         : Entity_Id;
         Use_RM_Size : Boolean;
         Result      : out Boolean;
         Explanation : out Unbounded_String);

      procedure Type_Has_No_Holes_Callback
        (Typ         : Entity_Id;
         Result      : out Boolean;
         Explanation : out Unbounded_String);
      --  This function is a wrapper for Type_Has_No_Holes_Internal, that can
      --  be used with the generic to traverse records and arrays.

      procedure Type_Has_No_Holes_Callback
        (Typ         : Entity_Id;
         Result      : out Boolean;
         Explanation : out Unbounded_String) is
      begin
         Type_Has_No_Holes_Internal (Typ, True, Result, Explanation);
      end Type_Has_No_Holes_Callback;

      procedure Recurse is new
        Check_Composite_Types_For_Holes (Type_Has_No_Holes_Callback);

      --------------------------------
      -- Type_Has_No_Holes_Internal --
      --------------------------------

      procedure Type_Has_No_Holes_Internal
        (Typ         : Entity_Id;
         Use_RM_Size : Boolean;
         Result      : out Boolean;
         Explanation : out Unbounded_String)
      is

         function Typ_Name return String is (Type_Name_For_Explanation (Typ));

         Typ_Size : Uint;

      begin

         if Is_Tagged_Type (Typ) then
            Result := False;
            Explanation :=
              To_Unbounded_String (Typ_Name & " is a tagged type");
            return;
         end if;

         if Is_Private_Type (Typ) then
            Result := False;
            Explanation :=
              To_Unbounded_String (Typ_Name & " is a private type");
            return;
         end if;

         if Is_Concurrent_Type (Typ) then
            Result := False;
            Explanation :=
              To_Unbounded_String (Typ_Name & " is a concurrent type");
            return;
         end if;

         if Has_Discriminants (Typ) then
            Result := False;
            Explanation :=
              To_Unbounded_String (Typ_Name & " has discriminants");
            return;
         end if;

         if Is_Scalar_Type (Typ) then
            Result := True;
            return;
         end if;

         if Use_RM_Size and then not Known_RM_Size (Typ) then
            Result := False;
            Explanation :=
              To_Unbounded_String (Typ_Name & " doesn't "
                                   & "have a Size representation clause or "
                                   & "aspect");
            return;
         end if;
         if not Use_RM_Size and then not Known_Esize (Typ)
         then
            Result := False;
            Explanation :=
              To_Unbounded_String (Typ_Name & " doesn't "
                                   & "have an Object_Size representation "
                                   & "clause or aspect");
            return;
         end if;

         if Use_RM_Size then
            Typ_Size := RM_Size (Typ);
         else
            Typ_Size := Esize (Typ);
         end if;

         Recurse (Typ, Typ_Size, Result, Explanation);
      end Type_Has_No_Holes_Internal;

   begin
      Type_Has_No_Holes_Internal (Typ, False, Result, Explanation);
   end Type_Has_No_Holes;

   ----------------------------------
   -- Is_Valid_Bitpattern_No_Holes --
   ----------------------------------

   procedure Is_Valid_Bitpattern_No_Holes (Typ         : Entity_Id;
                                           Result      : out Boolean;
                                           Explanation : out Unbounded_String)
   is
      --  The property Is_Valid_Bitpattern_No_Holes is *not* compositional.
      --  For example, an object of type U7:
      --
      --  type U7 is mod 2 ** 7;
      --  X : U7;
      --
      --  is considered to have a hole (the Size of X, or Object_Size of U7, is
      --  8, but the data only takes up 7 bits), while this type does not:

      --  type My_Rec is record
      --     X : U7;
      --     Y : Boolean;
      --  end record;

      --  In practice it means that for components, we need to use the RM_Size,
      --  and not the Object_Size of the type to carry out the checks in this
      --  function.

      procedure Is_Valid_Bitpattern_No_Holes_Internal
        (Typ         : Entity_Id;
         Use_RM_Size : Boolean;
         Result      : out Boolean;
         Explanation : out Unbounded_String);
      --  The internal version of the function. If Use_RM_Size is set to True,
      --  the RM_Size is used for size computations, otherwise the
      --  Object_Size/Esize is used.

      procedure Is_Valid_Bitpattern_No_Holes_Callback
        (Typ         : Entity_Id;
         Result      : out Boolean;
         Explanation : out Unbounded_String);

      -------------------------------------------
      -- Is_Valid_Bitpattern_No_Holes_Callback --
      -------------------------------------------

      procedure Is_Valid_Bitpattern_No_Holes_Callback
        (Typ         : Entity_Id;
         Result      : out Boolean;
         Explanation : out Unbounded_String)
      is
      begin
         Is_Valid_Bitpattern_No_Holes_Internal
           (Typ, True, Result, Explanation);
      end Is_Valid_Bitpattern_No_Holes_Callback;

      procedure Recurse is new Check_Composite_Types_For_Holes
        (Is_Valid_Bitpattern_No_Holes_Callback);

      -------------------------------------------
      -- Is_Valid_Bitpattern_No_Holes_Internal --
      -------------------------------------------

      procedure Is_Valid_Bitpattern_No_Holes_Internal
        (Typ         : Entity_Id;
         Use_RM_Size : Boolean;
         Result      : out Boolean;
         Explanation : out Unbounded_String)
      is

         function Typ_Name return String is (Type_Name_For_Explanation (Typ));

         Typ_Size : Uint;

      --  Start of processing for Is_Valid_Bitpattern_No_Holes_Internal

      begin
         --  Some valid IEEE 754 values are not allowed in SPARK, such as NaN

         if Is_Floating_Point_Type (Typ) then
            Result := False;
            Explanation :=
              To_Unbounded_String ("floating-point types have invalid bit "
                                   & "patterns for SPARK");
            return;
         end if;

         if Use_RM_Size and then not Known_RM_Size (Typ) then
            Result := False;
            Explanation :=
              To_Unbounded_String (Typ_Name & " doesn't "
                                   & "have a Size representation clause or "
                                   & "aspect");
            return;
         end if;
         if not Use_RM_Size and then not Known_Esize (Typ)
         then
            Result := False;
            Explanation :=
              To_Unbounded_String (Typ_Name & " doesn't "
                                   & "have an Object_Size representation "
                                   & "clause or aspect");
            return;
         end if;

         --  We always exclude invariants and predicates, as well as types with
         --  discriminants and tags, private types and concurrent types.

         if Invariant_Check_Needed (Typ)
           or else Has_Predicates (Typ)
         then
            Result := False;
            Explanation :=
              To_Unbounded_String (Typ_Name & " has invariants or predicates");
            return;
         end if;

         if Has_Discriminants (Typ) then
            Result := False;
            Explanation :=
              To_Unbounded_String (Typ_Name & " has discriminants");
            return;
         end if;

         if Is_Tagged_Type (Typ) then
            Result := False;
            Explanation :=
              To_Unbounded_String (Typ_Name & " is a tagged type");
            return;
         end if;

         if Is_Private_Type (Typ) then
            Result := False;
            Explanation :=
              To_Unbounded_String (Typ_Name & " is a private type");
            return;
         end if;

         if Is_Concurrent_Type (Typ) then
            Result := False;
            Explanation :=
              To_Unbounded_String (Typ_Name & " is a concurrent type");
            return;
         end if;

         if Use_RM_Size then
            Typ_Size := RM_Size (Typ);
         else
            Typ_Size := Esize (Typ);
         end if;
         --  Constrained scalar types are also excluded

         if Is_Scalar_Type (Typ) then
            declare
               R : constant Node_Id := Scalar_Range (Typ);
            begin
               pragma Assert (Compile_Time_Known_Value (Low_Bound (R)));
               pragma Assert (Compile_Time_Known_Value (High_Bound (R)));
               declare
                  Low        : constant Uint := Expr_Value (Low_Bound (R));
                  High       : constant Uint := Expr_Value (High_Bound (R));
                  Num_Values : constant Uint := UI_Add (UI_Sub (High, Low), 1);
               begin
                  if UI_Eq (UI_Expon (Uint_2, Typ_Size), Num_Values) then
                     Result := True;
                     Explanation := To_Unbounded_String ("");
                  else
                     Result := False;
                     Explanation :=
                       To_Unbounded_String
                         (Typ_Name & " has "
                          & UI_Image (Num_Values)
                          & " values but has "
                          & (if Use_RM_Size then "Size " else "Object_Size ")
                          & UI_Image (Typ_Size));
                  end if;
                  return;
               end;
            end;
         end if;

         Recurse (Typ, Typ_Size, Result, Explanation);
      end Is_Valid_Bitpattern_No_Holes_Internal;

   begin
      Is_Valid_Bitpattern_No_Holes_Internal (Typ, False, Result, Explanation);
   end Is_Valid_Bitpattern_No_Holes;

   ----------------------------
   -- Iterate_Applicable_DIC --
   ----------------------------

   procedure Iterate_Applicable_DIC (Ty : Entity_Id) is
      Rep_Ty : Entity_Id := Retysp (Ty);
      Proc   : Entity_Id;
   begin
      while Present (Rep_Ty) and then Has_DIC (Rep_Ty) loop
         Proc := Partial_DIC_Procedure (Rep_Ty);
         if Present (Proc) then
            Process_DIC_Expression
              (First_Formal (Proc),
               Get_Expr_From_Check_Only_Proc (Proc));
         end if;
         Rep_Ty := Parent_Type (Rep_Ty);
      end loop;
   end Iterate_Applicable_DIC;

   ---------------------------
   -- May_Need_DIC_Checking --
   ---------------------------

   function May_Need_DIC_Checking (E : Entity_Id) return Boolean is
     (Has_Own_DIC (E) and then Present (Partial_DIC_Procedure (E)));
   --  ??? has_own_dic returns true on a type with a DIC that defaults to True
   --  but no partial_DIC_procedure is created.

   ----------------------------------
   -- Needs_Default_Checks_At_Decl --
   ----------------------------------

   function Needs_Default_Checks_At_Decl (E : Entity_Id) return Boolean is
      Decl : constant Node_Id := Parent (E);

   begin
      --  If the type is not private, its default initialization will be
      --  checked when used.

      return Nkind (Decl) in N_Private_Extension_Declaration
                           | N_Private_Type_Declaration

        --  Classwide types cannot be default initialized

        and then not Is_Class_Wide_Type (E)

        --  To avoid duplicate checks, only check a partial view if its full
        --  view does not need the check.

        and then (if Is_Partial_View (E)
                  then Nkind (Parent (Full_View (E))) not in
                      N_Private_Extension_Declaration
                    | N_Private_Type_Declaration)

        --  Types with unknown discriminants cannot be default initialized

        and then not Has_Unknown_Discriminants (E);
   end Needs_Default_Checks_At_Decl;

   --------------------------------
   -- Might_Contain_Relaxed_Init --
   --------------------------------

   function Might_Contain_Relaxed_Init (Typ : Entity_Id) return Boolean is
      Rep_Ty : constant Entity_Id := Base_Retysp (Typ);
   begin
      if In_Relaxed_Init (Typ) then
         return True;
      elsif Is_Concurrent_Type (Rep_Ty) then
         return False;
      elsif Is_Scalar_Type (Rep_Ty) then
         return False;

      --  Expressions of tagged types and access types might contain relaxed
      --  init parts, as expressions partially initialized might be used
      --  inside aggregates or allocators. However, such expressions cannot be
      --  stored inside objects (as parts of tagged objects and types
      --  designated by access are not allowed to have relaxed initialization).
      --  So we prefer to consider that they should be always initialized, even
      --  if it can result in unnecessary initialization checks in corner
      --  cases.

      elsif Is_Tagged_Type (Rep_Ty) then
         return False;
      elsif Is_Access_Type (Rep_Ty) then
         return False;
      end if;

      --  If the type can be converted to a type which might contain
      --  components with relaxed initialization, we need relaxed
      --  initialization for it too.

      if Base_Retysp (Etype (Rep_Ty)) /= Rep_Ty
        and then Might_Contain_Relaxed_Init (Etype (Rep_Ty))
      then
         return True;

      --  Go over components composite types to know if they might contain
      --  relaxed init parts.

      elsif Is_Array_Type (Rep_Ty) then
         return Might_Contain_Relaxed_Init (Component_Type (Rep_Ty));
      elsif Is_Record_Type (Rep_Ty) then
         declare
            Comp : Entity_Id := First_Component (Rep_Ty);
         begin

            --  If it is a scalar type, a component of a record can only
            --  contain relaxed initialization if its type is annotated
            --  with relaxed initialization. Note that the same does not
            --  hold for arrays and access types which can be converted
            --  to types which are not of the same hierarchy.

            while Present (Comp) loop
               if Component_Is_Visible_In_SPARK (Comp)
                 and then (if Has_Scalar_Type (Etype (Comp))
                           then Has_Relaxed_Init (Etype (Comp))
                           else Might_Contain_Relaxed_Init (Etype (Comp)))
               then
                  return True;
               end if;
               Next_Component (Comp);
            end loop;
         end;
         return False;
      else
         return False;
      end if;
   end Might_Contain_Relaxed_Init;

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

   ------------------
   -- Num_Literals --
   ------------------

   function Num_Literals (Ty : Entity_Id) return Positive is
      Lit : Entity_Id := First_Literal (Ty);
      Count : Positive := 1;
   begin
      loop
         Next_Literal (Lit);
         exit when No (Lit);
         Count := Count + 1;
      end loop;
      return Count;
   end Num_Literals;

   -----------------
   -- Parent_Type --
   -----------------

   function Parent_Type (Ty : Entity_Id) return Entity_Id is
      Rep_Ty  : constant Entity_Id := Retysp (Ty);
      Decl    : constant Node_Id := Original_Node (Parent (Rep_Ty));
      --  Derived type definitions are sometimes rewritten into record
      --  definitions by the frontend.
      Sub_Ty  : constant Node_Id :=
        (if Nkind (Decl) = N_Subtype_Declaration
         then Subtype_Indication (Decl)
         elsif Nkind (Decl) = N_Full_Type_Declaration
         and then Nkind (Type_Definition (Decl)) =
           N_Derived_Type_Definition
         then Subtype_Indication (Type_Definition (Decl))
         else Empty);
      --  If Rep_Ty is a subtype, we need to use its declaration to find
      --  the next subtype in the derivation tree. Indeed, Etype on
      --  subtypes returns the base type.

      Next_Ty : constant Entity_Id :=
        (if Present (Sub_Ty)
         then Retysp
           (Entity
                (if Nkind (Sub_Ty) = N_Subtype_Indication
                 then Subtype_Mark (Sub_Ty)
                 else Sub_Ty))
         else Retysp (Etype (Rep_Ty)));
   begin
      if Next_Ty = Rep_Ty then
         return Empty;
      else
         return Next_Ty;
      end if;
   end Parent_Type;

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

   -----------------
   -- Root_Retysp --
   -----------------

   function Root_Retysp (E : Entity_Id) return Entity_Id is
      Result   : Entity_Id := Empty;
      Ancestor : Entity_Id :=
        (if Is_Class_Wide_Type (E) then Get_Specific_Type_From_Classwide (E)
         else E);
   begin
      --  Climb the type derivation chain as it is visible from SPARK code

      while Ancestor /= Result loop

         Result := Ancestor;
         Ancestor := Retysp (Etype (Result));
      end loop;

      return Result;
   end Root_Retysp;

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

   ---------------------------------
   -- Types_Have_Same_Known_Esize --
   ---------------------------------

   procedure Types_Have_Same_Known_Esize (A, B        : Entity_Id;
                                          Result      : out Boolean;
                                          Explanation : out Unbounded_String)
   is
   begin
      if not Known_Esize (A) then
         Result := False;
         Explanation :=
           To_Unbounded_String (Type_Name_For_Explanation (A) & " doesn't "
                                & "have an Object_Size representation "
                                & "clause or aspect");
         return;
      end if;
      if not Known_Esize (B) then
         Result := False;
         Explanation :=
           To_Unbounded_String (Type_Name_For_Explanation (B) & " doesn't "
                                & "have an Object_Size representation "
                                & "clause or aspect");
         return;
      end if;
      if not UI_Eq (Esize (A), Esize (B)) then
         Result := False;
         Explanation :=
           To_Unbounded_String ("Object_Sizes of "
                                & Type_Name_For_Explanation (A)
                                & " and " & Type_Name_For_Explanation (B)
                                & " differ");
         return;
      end if;
      Result := True;
      Explanation := Null_Unbounded_String;
   end Types_Have_Same_Known_Esize;

   -------------------------
   -- Unchecked_Full_Type --
   -------------------------

   function Unchecked_Full_Type (E : Entity_Id) return Entity_Id is
   begin
      if Is_Private_Type (E)
        and then Present (Underlying_Full_View (E))
      then
         return Unchecked_Full_Type (Underlying_Full_View (E));
      elsif Present (Full_View (E)) then
         return Unchecked_Full_Type (Full_View (E));

      --  Derived types without additional constraints might not have Full_View
      --  defined; search the on the Etype instead.

      elsif Is_Private_Type (E) then
         pragma Assert (Etype (E) /= E);
         return Unchecked_Full_Type (Etype (E));
      else
         return E;
      end if;
   end Unchecked_Full_Type;

   --------------------------------------
   -- Use_Predefined_Equality_For_Type --
   --------------------------------------

   function Use_Predefined_Equality_For_Type (Typ : Entity_Id) return Boolean
   is
     (not (Is_Record_Type (Unchecked_Full_Type (Typ))
      or else Is_Limited_View (Typ))
      or else No (Get_User_Defined_Eq (Base_Type (Typ))));

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
