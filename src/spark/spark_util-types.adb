------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                        S P A R K _ U T I L - T Y P E S                   --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                     Copyright (C) 2016-2023, AdaCore                     --
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
with Rtsfind;                    use Rtsfind;
with Sem_Eval;                   use Sem_Eval;
with Sinfo.Utils;                use Sinfo.Utils;
with SPARK_Definition;           use SPARK_Definition;
with SPARK_Definition.Annotate;  use SPARK_Definition.Annotate;
with SPARK_Util.Subprograms;     use SPARK_Util.Subprograms;

package body SPARK_Util.Types is

   function Type_Name_For_Explanation (Typ : Type_Kind_Id) return String
     is (if Is_Itype (Typ) then "anonymous type"
         else "type " & Source_Name (Typ))
     with Pre => Is_Type (Typ);
   --  This function computes a user-visible string to represent the type in
   --  argument.

   type Result_Type (Ok : Boolean := True) is record
      case Ok is
         when True  =>
            null;
         when False =>
            Explanation : Unbounded_String;
      end case;
   end record;
   --  Type to store a check result along with an explanation in case of
   --  failure.

   generic
      with function Type_Is_Suitable
     (Typ       : Type_Kind_Id;
      Use_Esize : Boolean) return Result_Type;

   procedure Suitable_For_UC_Gen
     (Typ         :     Type_Kind_Id;
      Use_Esize   :     Boolean;
      Result      : out Boolean;
      Explanation : out Unbounded_String);
   --  This function is used by Suitable_For_UC and Suitable_For_UC_Target.
   --  It checks that the types have no holes, and that each field has the
   --  property checked by the function Type_Is_Suitable. If Result is False,
   --  Explanation contains a string explaining why Typ is cannot be determined
   --  to be suitable for unchecked conversion.

   function Type_Is_Suitable_For_UC
     (Typ       : Type_Kind_Id;
      Use_Esize : Boolean) return Result_Type;
   --  Function to check the properties enforced on all subcomponents of a
   --  type "suitable for unchecked conversion" of SPARK RM 13.9.

   function Type_Is_Suitable_For_UC_Target
     (Typ       : Type_Kind_Id;
      Use_Esize : Boolean) return Result_Type;
   --  Function to check the properties enforced on all subcomponents of a
   --  type "suitable as a target of an unchecked conversion" of SPARK RM 13.9.

   procedure Check_Known_RM_Size
     (Typ         :     Type_Kind_Id;
      Result      : out Boolean;
      Explanation : out Unbounded_String);
   --  If the RM_Size of the type is known, set Result to True. Otherwise, set
   --  Result to False and save an explanation string in Explanation.

   procedure Check_Known_Esize
     (Typ         :     Type_Kind_Id;
      Result      : out Boolean;
      Explanation : out Unbounded_String);
   --  same as Check_Known_RM_Size, but for Esize

   type Test_Result is (Pass, Fail, Continue);

   generic
      with function Test (Typ : Type_Kind_Id) return Test_Result;
   function Traverse_Access_Parts (Typ : Type_Kind_Id) return Boolean;
   --  Generic function which applies test to all access subcomponents and
   --  subcomponents annotated with ownership of Typ,
   --  until one is found on which Test returns Pass. If Test returns
   --  Continue on an access subcomponent, the designated type is also searched
   --  for access subcomponents with the given property.

   function Ancestor_Declares_Iterable_Aspect
     (E      : Type_Kind_Id;
      Aspect : Node_Id)
      return Boolean;
   --  Shared code for Has_Iterable_Aspect_In_Spark/
   --  Declares_Iterable_Aspect: whether specific Aspect of E is
   --  declared by an anscestor. This ignores SPARK_Mode boundary.

   ---------------------------------------------
   -- Queries related to representative types --
   ---------------------------------------------

   function Base_Retysp (T : Type_Kind_Id) return Type_Kind_Id is
      E : Type_Kind_Id := Retysp (T);
   begin
      while not Is_Base_Type (E) loop
         E := Retysp (Base_Type (E));
      end loop;
      return E;
   end Base_Retysp;

   --  This function is similar to Sem_Eval.Is_Static_Subtype, except it only
   --  considers scalar subtypes (otherwise returns False), and looks past
   --  private types.

   ----------------------------------
   -- Has_OK_Static_Scalar_Subtype --
   ----------------------------------

   function Has_OK_Static_Scalar_Subtype (T : Type_Kind_Id) return Boolean is
      Under_T  : constant Type_Kind_Id := Underlying_Type (T);
      Base_T   : constant Type_Kind_Id := Base_Type (Under_T);
      Anc_Subt : Opt_Type_Kind_Id;

   begin
      if Base_T = Under_T then
         return True;

      else
         Anc_Subt := Ancestor_Subtype (Under_T);

         if Anc_Subt = Empty then
            Anc_Subt := Base_T;
         end if;

         return Has_OK_Static_Scalar_Subtype (Anc_Subt)
           and then Is_OK_Static_Expression (Type_Low_Bound (Under_T))
           and then Is_OK_Static_Expression (Type_High_Bound (Under_T));
      end if;
   end Has_OK_Static_Scalar_Subtype;

   ------------
   -- Retysp --
   ------------

   function Retysp (T : Type_Kind_Id) return Type_Kind_Id is
      Typ : Type_Kind_Id := T;

   begin
      --  Itypes may not be marked. Use their Etype.

      if Is_Itype (Typ) and then not Entity_Marked (Typ) then
         Typ := Etype (Typ);
      end if;

      pragma Assert (Entity_Marked (Typ));

      --  Incomplete types are only marked if their full view is not visible

      pragma Assert
        (not Is_Incomplete_Type (Typ) or else No (Full_View (Typ)));

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
            P_Typ   : constant Entity_Id :=
              (if Is_Full_View (Typ) then Partial_View (Typ) else Typ);
            Decl    : constant Node_Id := Parent (P_Typ);
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

   function Retysp_Kind (T : Type_Kind_Id) return Type_Kind is
     (Ekind (Retysp (T)));

   --------------------------
   -- Has_Scalar_Full_View --
   --------------------------

   function Has_Scalar_Full_View (Typ : Type_Kind_Id) return Boolean is
      Full_View : constant Type_Kind_Id := Unchecked_Full_Type (Typ);
   begin
      return Is_Scalar_Type (Full_View)
        or else (Full_View_Not_In_SPARK (Typ) and then Has_Predicates (Typ));
   end Has_Scalar_Full_View;

   ------------------------------------
   -- Has_Unconstrained_UU_Component --
   ------------------------------------

   function Has_Unconstrained_UU_Component (Typ : Type_Kind_Id) return Boolean
   is
      Rep_Ty : constant Type_Kind_Id := Root_Retysp (Typ);
      --  For tagged types, go to the root type. UU_Components cannot be
      --  contained in derivations, as this would be rejected in marking.

   begin
      if Is_Record_Type (Rep_Ty) then
         declare
            Comp : Node_Id := First_Component (Rep_Ty);
         begin
            while Present (Comp) loop
               if Component_Is_Visible_In_SPARK (Comp)
                 and then
                   ((Is_Unchecked_Union (Retysp (Etype (Comp)))
                     and then not Is_Constrained (Retysp (Etype (Comp))))
                    or else Has_Unconstrained_UU_Component (Etype (Comp)))
               then
                  return True;
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

   ---------------------------------
   -- Has_Visible_Type_Invariants --
   ---------------------------------

   function Has_Visible_Type_Invariants (Ty : Type_Kind_Id) return Boolean is
      Real_Node : constant Node_Id :=
        (if Is_Itype (Ty)
         then Associated_Node_For_Itype (Ty)
         else Ty);

   begin
      return Has_Invariants_In_SPARK (Ty)
        and then Is_Declared_In_Main_Unit_Or_Parent (Real_Node);
   end Has_Visible_Type_Invariants;

   -----------------------------
   -- Acts_As_Incomplete_Type --
   -----------------------------

   function Acts_As_Incomplete_Type (Ty : Type_Kind_Id) return Boolean is
     ((Is_Incomplete_Type (Ty)
      and then not From_Limited_With (Ty)
      and then Present (Full_View (Ty)))
      or else Is_Partial_View (Ty)
      or else
        (Is_Class_Wide_Type (Ty)
         and then not From_Limited_With (Ty)
         and then Nkind (Atree.Parent (Ty)) in
           N_Incomplete_Type_Declaration
         | N_Private_Type_Declaration));

   ------------------------------
   -- Check_DIC_At_Declaration --
   ------------------------------

   function Check_DIC_At_Declaration (E : Type_Kind_Id) return Boolean is
      Default_Init_Subp : constant E_Procedure_Id :=
        Partial_DIC_Procedure (E);
      Default_Init_Expr : constant N_Subexpr_Id :=
        Get_Expr_From_Check_Only_Proc (Default_Init_Subp);
      Init_Param        : constant Formal_Kind_Id :=
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

   -----------------------
   -- Check_Known_Esize --
   -----------------------

   procedure Check_Known_Esize
     (Typ         :     Type_Kind_Id;
      Result      : out Boolean;
      Explanation : out Unbounded_String)
   is
   begin
      if not Known_Esize (Typ) then
         Result := False;
         Explanation :=
           To_Unbounded_String (Type_Name_For_Explanation (Typ) & " doesn't "
                                & "have an Object_Size representation "
                                & "clause or aspect");
      else
         Result := True;
      end if;
   end Check_Known_Esize;

   -------------------------
   -- Check_Known_RM_Size --
   -------------------------

   procedure Check_Known_RM_Size
     (Typ         :     Type_Kind_Id;
      Result      : out Boolean;
      Explanation : out Unbounded_String)
   is
   begin
      if not Known_RM_Size (Typ) then
         Result := False;

         --  A Size representation clause cannot be added on the constrained
         --  array subtype of an unconstrained array type (unless both are
         --  introduced by the same declaration, in which case Typ is a first
         --  subtype). Instead, the array type can be specified as packed so
         --  that the size of its subtype is computed automatically.

         if Ekind (Typ) = E_Array_Subtype
           and then not Is_Constrained (Etype (Typ))
           and then not Is_First_Subtype (Typ)
         then
            if not Has_Pragma_Pack (Etype (Typ)) then
               Explanation :=
                 To_Unbounded_String
                   (Type_Name_For_Explanation (Etype (Typ))
                    & " doesn't have a Pack pragma or aspect");
            else
               Explanation :=
                 To_Unbounded_String
                   ("size of " & Type_Name_For_Explanation (Typ)
                    & " cannot be computed statically");
            end if;
         else
            Explanation :=
              To_Unbounded_String
                (Type_Name_For_Explanation (Typ)
                 & " doesn't have a Size representation clause or aspect");
         end if;
      else
         Result := True;
      end if;
   end Check_Known_RM_Size;

   --------------------------------
   -- Check_Needed_On_Conversion --
   --------------------------------

   function Check_Needed_On_Conversion
     (From, To : Type_Kind_Id)
      return Boolean
   is
      To_R   : constant Type_Kind_Id := Retysp (To);
      From_R : constant Type_Kind_Id := Retysp (From);
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

   -----------------------------------
   -- Contains_Access_Subcomponents --
   -----------------------------------

   function Contains_Access_Subcomponents (Typ : Type_Kind_Id) return Boolean
   is

      function Is_Access (Typ : Type_Kind_Id) return Test_Result is
        (if Is_Access_Type (Typ) then Pass else Fail);

      function Contains_Access_Subcomponents is new
        Traverse_Access_Parts (Is_Access);

   begin
      return Contains_Access_Subcomponents (Typ);
   end Contains_Access_Subcomponents;

   ------------------------------
   -- Contains_Allocated_Parts --
   ------------------------------

   function Contains_Allocated_Parts (Typ : Type_Kind_Id) return Boolean is

      function Access_Is_Allocated (Typ : Type_Kind_Id) return Test_Result is

         --  If Typ is a general access type, look at its designated type
        (if Is_General_Access_Type (Typ) then Continue

         --  Otherwise, the type contains allocated parts if it is a pool
         --  specific access type, an anonymous access-to-object type, or
         --  if it has an ownership annotation and it needs reclamation.

         elsif (Is_Access_Object_Type (Typ)
            and then (not Is_Access_Constant (Typ)
              or else Is_Anonymous_Access_Type (Typ)))
         or else (Has_Ownership_Annotation (Typ)
           and then Needs_Reclamation (Typ))
         then Pass else Fail);

      function Contains_Allocated_Parts is new
        Traverse_Access_Parts (Access_Is_Allocated);

   begin
      return Contains_Allocated_Parts (Typ);
   end Contains_Allocated_Parts;

   ---------------------------------
   -- Contains_Relaxed_Init_Parts --
   ---------------------------------

   function Contains_Relaxed_Init_Parts
     (Typ        : Type_Kind_Id;
      Ignore_Top : Boolean := False)
      return Boolean
   is
      Rep_Ty : constant Type_Kind_Id := Retysp (Typ);
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
               Comp : Opt_E_Component_Id := First_Component (Rep_Ty);
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
           (Is_Incomplete_Or_Private_Type (Rep_Ty)
            or else Is_Scalar_Type (Rep_Ty));
         return False;
      end if;
   end Contains_Relaxed_Init_Parts;

   --------------------------------
   -- Contains_Only_Relaxed_Init --
   --------------------------------

   function Contains_Only_Relaxed_Init (Typ : Type_Kind_Id) return Boolean is
      Rep_Ty : constant Type_Kind_Id := Retysp (Typ);
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
               Comp             : Opt_E_Component_Id :=
                 First_Component (Rep_Ty);
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
           (Is_Incomplete_Or_Private_Type (Rep_Ty)
            or else Is_Scalar_Type (Rep_Ty));
         return False;
      end if;
   end Contains_Only_Relaxed_Init;

   ------------------------
   -- Copy_Requires_Init --
   ------------------------

   function Copy_Requires_Init (Typ : Type_Kind_Id) return Boolean is
     (Has_Scalar_Full_View (Typ)
      or else (Has_Predicates (Typ)
        and then Predicate_Requires_Initialization (Typ)));

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

   ----------------------------------
   -- Find_View_For_Default_Checks --
   ----------------------------------

   function Find_View_For_Default_Checks
     (E : Type_Kind_Id)
      return Opt_Type_Kind_Id
   is
      Typ  : Entity_Id := Retysp (E);
   begin

      --  Types whose full view is not in Spark do not need specific checks
      if Nkind (Parent (Typ)) in N_Private_Extension_Declaration
                               | N_Private_Type_Declaration
      then
         return Empty;
      end if;

      loop
         Typ := Partial_View (Typ);

         --  Types with no private view do not need specific checks
         if No (Typ) then
            return Empty;
         end if;

         if Nkind (Parent (Typ)) in N_Private_Extension_Declaration
                                  | N_Private_Type_Declaration
         then
            --  Types whose private view has unknown discriminants,
            --  including the implicit tag for class-wide type,
            --  cannot be default initialized
            if Is_Class_Wide_Type (Typ) or else Has_Unknown_Discriminants (Typ)
            then
               return Empty;
            else
               return Typ;
            end if;
         end if;
      end loop;

   end Find_View_For_Default_Checks;

   -------------------------
   -- Find_Predicate_Item --
   -------------------------

   procedure Find_Predicate_Item
     (Ty       :        Type_Kind_Id;
      Rep_Item : in out Node_Id)
   is
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

   function Get_Parent_Type_If_Check_Needed
     (N : N_Declaration_Id)
      return Opt_Type_Kind_Id
   is
   begin
      if Nkind (N) = N_Full_Type_Declaration then
         declare
            T_Def : constant Node_Id := Type_Definition (N);
         begin
            case Nkind (T_Def) is
               when N_Subtype_Indication =>
                  raise Program_Error;

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

   function Get_Specific_Type_From_Classwide (E : Class_Wide_Kind_Id)
                                              return Type_Kind_Id
   is
      Specific_Type : constant Type_Kind_Id := Etype (Base_Type (E));

   begin
      if Is_Full_View (Specific_Type) then
         return Partial_View (Specific_Type);
      else
         return Specific_Type;
      end if;
   end Get_Specific_Type_From_Classwide;

   ------------------------------
   -- Get_Constraint_For_Discr --
   ------------------------------

   function Get_Constraint_For_Discr
     (Ty    : Type_Kind_Id;
      Discr : E_Discriminant_Id)
      return N_Subexpr_Id
   is
      Current : E_Discriminant_Id := First_Discriminant (Ty);
      Elmt    : Elmt_Id := First_Elmt (Discriminant_Constraint (Ty));
   begin
      while Current /= Discr loop
         Next_Discriminant (Current);
         Next_Elmt (Elmt);
      end loop;
      return Node (Elmt);
   end Get_Constraint_For_Discr;

   -------------------------
   -- Get_User_Defined_Eq --
   -------------------------

   function Get_User_Defined_Eq (Typ : Type_Kind_Id) return Opt_E_Function_Id
   is
      Eq : constant Entity_Id := Sem_Util.Get_User_Defined_Equality
        (if Is_Full_View (Typ) then Partial_View (Typ) else Typ);

   begin
      --  Ignore predefined equality of tagged types

      if Present (Eq) and then Is_Tagged_Predefined_Eq (Eq) then
         return Empty;
      elsif Present (Eq)
        and then Present (Einfo.Utils.Renamed_Entity (Eq))
      then
         return Einfo.Utils.Renamed_Entity (Eq);
      end if;

      return Eq;
   end Get_User_Defined_Eq;

   -----------------------------
   -- Has_Invariants_In_SPARK --
   -----------------------------

   function Has_Invariants_In_SPARK (E : Type_Kind_Id) return Boolean is
     (Has_Own_Invariants (E)
      and then Is_Base_Type (E)
      and then (if Is_Partial_View (E) then Entity_In_SPARK (Full_View (E))));

   ---------------------------------------
   -- Ancestor_Declares_Iterable_Aspect --
   ---------------------------------------

   function Ancestor_Declares_Iterable_Aspect
     (E      : Type_Kind_Id;
      Aspect : Node_Id)
      return Boolean
   is
      Cursor : Type_Kind_Id := E;
   begin
      while Is_Partial_View (Cursor) loop
         Cursor := Full_View (Cursor);
      end loop;
      if Is_First_Subtype (Cursor) then
         Cursor := Base_Type (Cursor);
      end if;
      return not Is_Nouveau_Type (Cursor)
        and then Underlying_Type (Etype (Cursor)) /= Cursor
        and then Find_Aspect (Etype (Cursor), Aspect_Iterable) = Aspect;
   end Ancestor_Declares_Iterable_Aspect;

   ----------------------------------
   -- Has_Iterable_Aspect_In_SPARK --
   ----------------------------------

   function Has_Iterable_Aspect_In_SPARK (E : Type_Kind_Id) return Boolean is
      Top_Aspect : constant Node_Id := Find_Aspect (E, Aspect_Iterable);
      Cursor     : Type_Kind_Id := Retysp (E);
   begin
      if No (Top_Aspect) then
         return False;
      end if;
      while not Is_Nouveau_Type (Cursor)
        and then Underlying_Type (Etype (Cursor)) /= Cursor
      loop
         Cursor := Retysp (Etype (Cursor));
         if Find_Aspect (Cursor, Aspect_Iterable) /= Top_Aspect then
            return True;
         end if;
      end loop;
      --  If an out-of-SPARK ancestor declares the Iterable Aspect,
      --  the aspect should not be visible in SPARK
      --  (happens in some corner cases).
      return not Ancestor_Declares_Iterable_Aspect (Cursor, Top_Aspect);
   end Has_Iterable_Aspect_In_SPARK;

   ------------------------------
   -- Declares_Iterable_Aspect --
   ------------------------------

   function Declares_Iterable_Aspect (E : Type_Kind_Id) return Boolean
   is
      Top_Aspect : constant Node_Id := Find_Aspect (E, Aspect_Iterable);
   begin
      return Present (Top_Aspect)
        and then not Is_Itype (E)
        and then not Ancestor_Declares_Iterable_Aspect (E, Top_Aspect);
   end Declares_Iterable_Aspect;

   ------------------------
   -- Has_Private_Fields --
   ------------------------

   function Has_Private_Fields (E : Type_Kind_Id) return Boolean is
      Ty : constant Type_Kind_Id := Retysp (E);
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

      return Is_Incomplete_Or_Private_Type (Ty);
   end Has_Private_Fields;

   ----------------------------
   -- Invariant_Check_Needed --
   ----------------------------

   function Invariant_Check_Needed (Ty : Type_Kind_Id) return Boolean is
      Rep_Ty  : constant Type_Kind_Id := Retysp (Ty);
      Current : Type_Kind_Id := Rep_Ty;
      Parent  : Type_Kind_Id;

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

      --  Check for invariants on components

      if Is_Array_Type (Rep_Ty) then
         return Invariant_Check_Needed (Component_Type (Rep_Ty));

      elsif Is_Incomplete_Or_Private_Type (Rep_Ty)
        or else Is_Record_Type (Rep_Ty)
        or else Is_Concurrent_Type (Rep_Ty)
      then
         if Has_Discriminants (Rep_Ty) then
            declare
               Discr : Opt_E_Discriminant_Id := First_Discriminant (Rep_Ty);
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

      --  We stop the search at access-to-incomplete types, as they might
      --  not be marked yet. This is possible because there is a tool
      --  limitation which disallows access to incomplete types if they need
      --  an invariant check.

      elsif Is_Access_Type (Rep_Ty)
        and then not Is_Access_Subprogram_Type (Rep_Ty)
      then
         declare
            Des_Ty : constant Entity_Id := Directly_Designated_Type
              (Base_Retysp (Rep_Ty));
            --  Use the base type as some subtypes of access to incomplete
            --  types introduced by the frontend designate record subtypes
            --  instead.
         begin
            return not Acts_As_Incomplete_Type (Des_Ty)
              and then Invariant_Check_Needed (Des_Ty);
         end;
      end if;
      return False;
   end Invariant_Check_Needed;

   -------------
   -- Is_Deep --
   -------------

   function Is_Deep (Typ : Type_Kind_Id) return Boolean is
      function Test_Access_Type (Typ : Type_Kind_Id) return Test_Result is
        (if Is_Access_Object_Type (Typ)
         and then (not Is_Access_Constant (Typ)
           or else Is_Anonymous_Access_Type (Typ))
         then Pass
         elsif Has_Ownership_Annotation (Typ)
         then Pass
         else Fail);
      --  Access to subprograms are not subjected to ownership rules, nor
      --  are access-to-constant types, unless they are observers
      --  (anonymous access-to-constant types). Private type might be subjected
      --  to ownership rules if they have an ownership annotation.

      function Is_Deep is new Traverse_Access_Parts (Test_Access_Type);
   begin
      return Is_Deep (Typ);
   end Is_Deep;

   -----------------------------------
   -- Is_Derived_Type_With_Null_Ext --
   -----------------------------------

   function Is_Derived_Type_With_Null_Ext (Ty : Type_Kind_Id) return Boolean is
      Decl : constant Node_Id := Enclosing_Declaration (Retysp (Ty));
   begin
      if No (Decl) or else Nkind (Decl) /= N_Full_Type_Declaration then
         return False;
      end if;

      declare
         Def : constant Node_Id := Type_Definition (Decl);
      begin
         return Nkind (Def) = N_Derived_Type_Definition
           and then Null_Present (Record_Extension_Part (Def));
      end;
   end Is_Derived_Type_With_Null_Ext;

   ----------------------------
   -- Is_General_Access_Type --
   ----------------------------

   function Is_General_Access_Type (T : Type_Kind_Id) return Boolean is
      Base : Type_Kind_Id := T;
   begin
      if Ekind (Base) = E_Access_Subtype then
         Base := Base_Type (Base);

         if Is_Private_Type (Base) then
            Base := Full_View (Base);
         end if;

         pragma Assert (Is_Access_Type (Base));
      end if;

      return Ekind (Base) = E_General_Access_Type
        and then not Is_Access_Constant (Base);
   end Is_General_Access_Type;

   -------------------
   -- Is_Null_Range --
   -------------------

   function Is_Null_Range (T : Type_Kind_Id) return Boolean is
     (Is_Discrete_Type (T)
      and then Has_OK_Static_Scalar_Subtype (T)
      and then Expr_Value (Type_Low_Bound (T)) >
          Expr_Value (Type_High_Bound (T)));

   ----------------------
   -- Is_Standard_Type --
   ----------------------

   --  E might be a standard type or the implicit base type of such a standard
   --  type.
   function Is_Standard_Type (E : Type_Kind_Id) return Boolean is
     (for some S_Type in S_Types =>
         E = Standard_Entity (S_Type) or E = Etype (Standard_Entity (S_Type)));

   ------------------------------
   -- Is_Standard_Boolean_Type --
   ------------------------------

   function Is_Standard_Boolean_Type (E : Type_Kind_Id) return Boolean is
     (E = Standard_Boolean
      or else
        (Ekind (E) = E_Enumeration_Subtype
         and then Etype (E) = Standard_Boolean
         and then Scalar_Range (E) = Scalar_Range (Standard_Boolean)
         and then not Has_Predicates (E)));

   --------------------------
   -- Is_Static_Array_Type --
   --------------------------

   function Is_Static_Array_Type (E : Type_Kind_Id) return Boolean is
     (Is_Array_Type (E)
        and then Is_Constrained (E)
        and then Has_Static_Array_Bounds (E));

   ----------------------------
   -- Is_System_Address_Type --
   ----------------------------

   function Is_System_Address_Type (E : Type_Kind_Id) return Boolean is
      (Is_RTE (E, RE_Address));

   ----------------------------
   -- Iterate_Applicable_DIC --
   ----------------------------

   procedure Iterate_Applicable_DIC (Ty : Type_Kind_Id) is
      Rep_Ty : Opt_Type_Kind_Id := Retysp (Ty);
      Proc   : Opt_E_Procedure_Id;
   begin
      while Present (Rep_Ty) and then Has_DIC (Rep_Ty) loop

         --  Go to base type, default initial conditions cannot be specified on
         --  subtypes.

         Rep_Ty := Base_Retysp (Rep_Ty);
         Proc := Partial_DIC_Procedure (Rep_Ty);
         if Present (Proc) then
            Process_DIC_Expression
              (First_Formal (Proc),
               Get_Expr_From_Check_Only_Proc (Proc));
         end if;

         --  Go to parent subtype

         Rep_Ty := Parent_Retysp (Rep_Ty);
      end loop;
   end Iterate_Applicable_DIC;

   -----------------------------------
   -- Iterate_Applicable_Predicates --
   -----------------------------------

   procedure Iterate_Applicable_Predicates (Ty : Type_Kind_Id) is
      Rep_Ty : Entity_Id := Retysp (Ty);

      Save_Current_Error_Node : constant Node_Id := Current_Error_Node;
      --  Predicate handling in GNAT is complicated, so if we crash, then at
      --  least try to precisely show where the problematic type is located.

   begin
      --  Go through the ancestors of Ty to collect all applicable predicates

      while Has_Predicates (Rep_Ty) loop
         Current_Error_Node := Rep_Ty;

         declare
            Pred_Fun : constant Entity_Id := Predicate_Function (Rep_Ty);

         begin
            --  There might be no predicate functions if the full view of
            --  Rep_Ty is an Itype. In this case, the predicate is inherited,
            --  ignore it.

            if No (Pred_Fun) then
               null;
            else
               if Entity_In_SPARK (Pred_Fun) then
                  declare
                     Expr : constant Node_Id := Get_Expr_From_Return_Only_Func
                       (Pred_Fun);
                  begin
                     --  Ignore predicates which are inherited from parents,
                     --  they will be traversed too.

                     if not Is_Predicate_Function_Call (Expr) then
                        Process_Pred_Expression
                          (Type_Instance   => First_Formal (Pred_Fun),
                           Pred_Expression => Expr);
                     end if;
                  end;
               end if;

               --  Go directly to the first type on which the predicate applies
               --  using the type of the first formal of the predicate
               --  function.

               Rep_Ty := Retysp (Etype (First_Formal (Pred_Fun)));
            end if;
         end;

         --  Go to the next type in the derivation tree of Rep_Ty to continue
         --  the search.

         Rep_Ty := Parent_Retysp (Rep_Ty);
         exit when No (Rep_Ty);
      end loop;

      Current_Error_Node := Save_Current_Error_Node;
   end Iterate_Applicable_Predicates;

   ---------------------------
   -- May_Need_DIC_Checking --
   ---------------------------

   function May_Need_DIC_Checking (E : Type_Kind_Id) return Boolean is
     (Has_Own_DIC (E) and then Present (Partial_DIC_Procedure (E)));
   --  ??? has_own_dic returns true on a type with a DIC that defaults to True
   --  but no partial_DIC_procedure is created.

   --------------------------------
   -- Might_Contain_Relaxed_Init --
   --------------------------------

   function Might_Contain_Relaxed_Init (Typ : Type_Kind_Id) return Boolean is
      Rep_Ty : constant Type_Kind_Id := Base_Retysp (Typ);
   begin
      if Has_Relaxed_Init (Typ) then
         return False;
      elsif In_Relaxed_Init (Typ) then
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
            Comp : Opt_E_Component_Id := First_Component (Rep_Ty);
         begin
            --  If it is a scalar type, a component of a record can only
            --  contain relaxed initialization if its type is annotated
            --  with relaxed initialization. Note that the same does not
            --  hold for arrays and access types which can be converted
            --  to types which are not of the same hierarchy.

            while Present (Comp) loop
               if Component_Is_Visible_In_SPARK (Comp)
                 and then not Has_Scalar_Type (Etype (Comp))
                 and then Might_Contain_Relaxed_Init (Etype (Comp))
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

   function Nth_Index_Type
     (E   : Array_Kind_Id;
      Dim : Positive)
      return Type_Kind_Id
   is
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

   function Num_Literals (Ty : Enumeration_Kind_Id) return Positive is
      Lit   : Opt_E_Enumeration_Literal_Id := First_Literal (Ty);
      Count : Positive := 1;
   begin
      loop
         Next_Literal (Lit);
         exit when No (Lit);
         Count := Count + 1;
      end loop;
      return Count;
   end Num_Literals;

   -------------------
   -- Parent_Retysp --
   -------------------

   function Parent_Retysp (Ty : Type_Kind_Id) return Opt_Type_Kind_Id is
      Rep_Ty  : constant Type_Kind_Id := Retysp (Ty);
      Next_Ty : constant Type_Kind_Id :=
        Retysp (Parent_Type (Rep_Ty));
   begin
      if Next_Ty = Rep_Ty then
         return Empty;
      else
         return Next_Ty;
      end if;
   end Parent_Retysp;

   -----------------
   -- Parent_Type --
   -----------------

   function Parent_Type (Ty : Type_Kind_Id) return Opt_Type_Kind_Id is
      Decl   : constant Node_Id := Original_Node (Parent (Ty));
      --  Derived type definitions are sometimes rewritten into record
      --  definitions by the frontend.
      Sub_Ty : constant Node_Id :=
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

   begin
      return (if Present (Sub_Ty)
              then Entity
                (if Nkind (Sub_Ty) = N_Subtype_Indication
                 then Subtype_Mark (Sub_Ty)
                 else Sub_Ty)
              else Etype (Ty));
   end Parent_Type;

   ---------------------------------------
   -- Private_Declarations_Of_Prot_Type --
   ---------------------------------------

   function Private_Declarations_Of_Prot_Type
     (E : Protected_Kind_Id)
      return List_Id
   is (Private_Declarations (Protected_Type_Definition (Base_Type (E))));

   -----------------------------------
   -- Predefined_Eq_Uses_Pointer_Eq --
   -----------------------------------

   function Predefined_Eq_Uses_Pointer_Eq (Ty : Type_Kind_Id) return Boolean is

      function Uses_Pointer_Eq_Comp (Ty : Type_Kind_Id) return Boolean is
        (not (Is_Record_Type (Unchecked_Full_Type (Ty))
              and then Present (Get_User_Defined_Eq (Base_Type (Ty))))
         and then Predefined_Eq_Uses_Pointer_Eq (Ty));
      --  The predefined equality on pointer is used for a component of type Ty
      --  if the predefined equality is used for components of this type and
      --  this equality uses predefined equality on pointers.

      Spec_Ty : constant Entity_Id :=
        (if Is_Class_Wide_Type (Retysp (Ty))
         then Get_Specific_Type_From_Classwide (Retysp (Ty))
         else Ty);
      Rep_Ty  : constant Type_Kind_Id := Retysp (Spec_Ty);

   begin
      --  The predefined equality on a class-wide type uses the primitive
      --  equality on its specific view.

      if Is_Class_Wide_Type (Retysp (Ty))
        and then Present (Get_User_Defined_Eq (Spec_Ty))
      then
         return False;
      elsif Is_Access_Type (Rep_Ty) then
         return True;
      elsif Is_Array_Type (Rep_Ty) then
         return Uses_Pointer_Eq_Comp (Component_Type (Rep_Ty));
      elsif Is_Record_Type (Rep_Ty) then
         declare
            Is_Tagged : constant Boolean := Is_Tagged_Type (Rep_Ty);
            Base      : constant Type_Kind_Id := Base_Retysp (Rep_Ty);
            Parent    : constant Type_Kind_Id := Retysp (Etype (Base));

         begin
            --  Check if a pointer equality is used for one of the visible
            --  components of Ty. For tagged types, only consider components
            --  which are not in the parent type as the primitive equality of
            --  the parent type will be used for its components.

            if not Is_Incomplete_Or_Private_Type (Base) then
               declare
                  Comp : Entity_Id := First_Component (Rep_Ty);
               begin
                  while Present (Comp) loop
                     if Component_Is_Visible_In_SPARK (Comp)
                       and then
                         (not Is_Tagged
                          or else Retysp
                            (Scope (Original_Record_Component (Comp))) = Base)
                       and then Uses_Pointer_Eq_Comp (Etype (Comp))
                     then
                        return True;
                     end if;

                     pragma Assert
                       (if Component_Is_Visible_In_SPARK (Comp)
                          and then Is_Tagged
                          and then Retysp
                            (Scope (Original_Record_Component (Comp))) /= Base
                        then Present
                          (Search_Component_By_Name (Parent, Comp)));
                     Next_Component (Comp);
                  end loop;
               end;
            end if;

            --  If the type is tagged, we need to check components inherited
            --  from the ancestor.

            if Is_Tagged then
               return Parent /= Base
                 and then No (Get_User_Defined_Eq (Parent))
                 and then Predefined_Eq_Uses_Pointer_Eq (Parent);
            else
               return False;
            end if;
         end;
      else
         pragma Assert
           (Ekind (Rep_Ty) in Incomplete_Or_Private_Kind | Scalar_Kind);
         return False;
      end if;
   end Predefined_Eq_Uses_Pointer_Eq;

   ---------------------------------------
   -- Predicate_Requires_Initialization --
   ---------------------------------------

   function Predicate_Requires_Initialization
     (Ty : Type_Kind_Id) return Boolean
   is
      Found : exception;

      procedure Requires_Initialization
        (Type_Instance   : Formal_Kind_Id;
         Pred_Expression : Node_Id);
      --  Raise Found if the predicate requires an initialization check. For
      --  now, we consider that all predicates require initialization checks
      --  unless they are defined on a type annotated with
      --  Relaxed_Initialization.

      -----------------------------
      -- Requires_Initialization --
      -----------------------------

      procedure Requires_Initialization
        (Type_Instance   : Formal_Kind_Id;
         Pred_Expression : Node_Id)
      is
         pragma Unreferenced (Pred_Expression);
      begin
         if not Has_Relaxed_Init (Etype (Type_Instance)) then
            raise Found;
         end if;
      end Requires_Initialization;

      procedure One_Predicate_Requires_Initialization is new
        Iterate_Applicable_Predicates (Requires_Initialization);
   begin
      One_Predicate_Requires_Initialization (Ty);
      return False;
   exception
      when Found =>
         return True;
   end Predicate_Requires_Initialization;

   ---------------------------------------
   -- Private_Declarations_Of_Task_Type --
   ---------------------------------------

   function Private_Declarations_Of_Task_Type
     (E : E_Task_Type_Id)
      return List_Id
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

   function Protected_Body
     (E : Protected_Kind_Id)
      return Opt_N_Protected_Body_Id
   is
      Ptr : constant Node_Id := Parent (E);
   begin
      pragma Assert (Nkind (Ptr) = N_Protected_Type_Declaration);
      return Parent (Corresponding_Body (Ptr));
   end Protected_Body;

   -------------------------------
   -- Protected_Type_Definition --
   -------------------------------

   function Protected_Type_Definition
     (E : Protected_Kind_Id)
      return Opt_N_Protected_Definition_Id
   is
      Decl : constant Node_Id := Parent (E);
      pragma Assert (Nkind (Decl) = N_Protected_Type_Declaration);

   begin
      return Protected_Definition (Decl);
   end Protected_Type_Definition;

   ---------------------------------
   -- Requires_Interrupt_Priority --
   ---------------------------------

   function Requires_Interrupt_Priority
     (E : Protected_Kind_Id)
      return Boolean
   is
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

   function Root_Retysp (E : Type_Kind_Id) return Type_Kind_Id is
      Result   : Opt_Type_Kind_Id := Empty;
      Ancestor : Type_Kind_Id :=
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

   function Static_Array_Length (E : Array_Kind_Id; Dim : Positive) return Uint
   is
   begin
      if Ekind (E) = E_String_Literal_Subtype then
         return String_Literal_Length (E);
      else
         declare
            F_Index : constant Type_Kind_Id := Nth_Index_Type (E, Dim);

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

   ---------------------
   -- Suitable_For_UC --
   ---------------------

   procedure Suitable_For_UC
     (Typ         :     Type_Kind_Id;
      Use_Esize   :     Boolean;
      Result      : out Boolean;
      Explanation : out Unbounded_String)
   is
      procedure Suitable is
        new Suitable_For_UC_Gen (Type_Is_Suitable_For_UC);
   begin
      Suitable (Typ, Use_Esize, Result, Explanation);
   end Suitable_For_UC;

   -------------------------
   -- Suitable_For_UC_Gen --
   -------------------------

   procedure Suitable_For_UC_Gen
     (Typ         :     Type_Kind_Id;
      Use_Esize   :     Boolean;
      Result      : out Boolean;
      Explanation : out Unbounded_String)
   is

      procedure Suitable_For_UC_Rec
        (Typ         :     Type_Kind_Id;
         Result      : out Boolean;
         Size        : out Uint;
         Explanation : out Unbounded_String;
         Use_Esize   :     Boolean := False);
      --  Traverse the type and all its subcomponents recursively

      -------------------------
      -- Suitable_For_UC_Rec --
      -------------------------

      procedure Suitable_For_UC_Rec
        (Typ         :     Type_Kind_Id;
         Result      : out Boolean;
         Size        : out Uint;
         Explanation : out Unbounded_String;
         Use_Esize   :     Boolean := False)
      is
         function Typ_Name return String is (Type_Name_For_Explanation (Typ));
      begin
         --  Default initialization for Codepeer
         Size := Uint_0;

         declare
            Check_Result : constant Result_Type :=
              Type_Is_Suitable (Typ, Use_Esize);
         begin
            if not Check_Result.Ok then
               Result := False;
               Explanation := Check_Result.Explanation;
               return;
            end if;
         end;

         if Is_Array_Type (Typ) then
            if not Is_Constrained (Typ) then
               Result := False;
               Explanation :=
                 To_Unbounded_String ("can't determine size for "
                                      & "unconstrained array " & Typ_Name);
               return;

            elsif not Compile_Time_Known_Bounds (Typ) then
               Result := False;
               Explanation :=
                 To_Unbounded_String ("bounds of " & Typ_Name & " are "
                                      & "not known at compile time");
               return;
            end if;

            declare
               Comp_Typ  : constant Type_Kind_Id :=
                 Retysp (Component_Type (Typ));
               Comp_Size : Uint;
               Index     : Node_Id;

            begin
               Suitable_For_UC_Rec (Comp_Typ, Result, Comp_Size, Explanation);
               if not Result then
                  return;
               end if;

               Size := Comp_Size;
               Index := First_Index (Typ);
               while Present (Index) loop
                  declare
                     Rng : constant Node_Id := Get_Range (Index);
                  begin
                     Size :=
                       Size *
                         (Expr_Value (High_Bound (Rng)) -
                            Expr_Value (Low_Bound (Rng)) + 1);
                     Next_Index (Index);
                  end;
               end loop;
            end;

         elsif Is_Record_Type (Typ) then
            declare
               Comp : Opt_E_Component_Id := First_Component (Typ);
            begin
               while Present (Comp) loop
                  declare
                     Comp_Ty   : constant Type_Kind_Id :=
                       Retysp (Etype (Comp));
                     Comp_Size : Uint;
                  begin
                     Suitable_For_UC_Rec
                       (Comp_Ty, Result, Comp_Size, Explanation);
                     if not Result then
                        return;
                     end if;
                     Size := Size + Comp_Size;
                  end;
                  Next_Component (Comp);
               end loop;
            end;

         else
            pragma Assert (Is_Scalar_Type (Typ));

            --  The size of scalar types is always known statically
            pragma Assert (Known_Esize (Typ) and Known_RM_Size (Typ));
            Size := (if Use_Esize then Esize (Typ) else RM_Size (Typ));
         end if;

         Result      := True;
         Explanation := Null_Unbounded_String;
      end Suitable_For_UC_Rec;

      function Typ_Name return String is (Type_Name_For_Explanation (Typ));

      Typ_Size : Uint;

   --  Start of processing for Suitable_For_UC_Gen

   begin
      Suitable_For_UC_Rec (Typ, Result, Typ_Size, Explanation, Use_Esize);
      if not Result then
         return;
      end if;

      if Use_Esize then
         Check_Known_Esize (Typ, Result, Explanation);
         if not Result then
            return;
         end if;
         if Esize (Typ) = Typ_Size then
            Result := True;
         else
            Result := False;
            Explanation :=
              To_Unbounded_String
                (Typ_Name & " has minimal size " & UI_Image (Typ_Size)
                 & ", but Object_Size was declared as "
                 & UI_Image (Esize (Typ)));
         end if;

      else
         Check_Known_RM_Size (Typ, Result, Explanation);
         if not Result then
            return;
         end if;
         if RM_Size (Typ) = Typ_Size then
            Result := True;
         else
            Result := False;
            Explanation :=
              To_Unbounded_String
                (Typ_Name & " has minimal size " & UI_Image (Typ_Size)
                 & ", but Size was declared as "
                 & UI_Image (RM_Size (Typ)));
         end if;
      end if;
   end Suitable_For_UC_Gen;

   ----------------------------
   -- Suitable_For_UC_Target --
   ----------------------------

   procedure Suitable_For_UC_Target
     (Typ         :     Type_Kind_Id;
      Use_Esize   :     Boolean;
      Result      : out Boolean;
      Explanation : out Unbounded_String)
   is
      procedure Suitable is
        new Suitable_For_UC_Gen (Type_Is_Suitable_For_UC_Target);
   begin
      Suitable (Typ, Use_Esize, Result, Explanation);
   end Suitable_For_UC_Target;

   ---------------
   -- Task_Body --
   ---------------

   function Task_Body (E : E_Task_Type_Id) return Opt_N_Task_Body_Id is
      Decl    : constant N_Task_Type_Declaration_Id := Parent (E);
      Body_Id : constant Entity_Id := Corresponding_Body (Decl);
   begin
      if Present (Body_Id) then
         return Parent (Body_Id);
      else
         return Empty;
      end if;
   end Task_Body;

   ----------------------
   -- Task_Body_Entity --
   ----------------------

   function Task_Body_Entity (E : E_Task_Type_Id) return Opt_E_Task_Body_Id
   is
      T_Body : constant Node_Id := Task_Body (E);
   begin
      if Present (T_Body) then
         pragma Assert (Present (Defining_Identifier (T_Body)));
         return Defining_Identifier (T_Body);
      else
         return Empty;
      end if;
   end Task_Body_Entity;

   ---------------------------
   -- Traverse_Access_Parts --
   ---------------------------

   function Traverse_Access_Parts (Typ : Type_Kind_Id) return Boolean is
      Seen : Node_Sets.Set;
      --  Set of access types already traversed. This is used to avoid infinite
      --  recursion on recursive structures.

      function Traverse_Access_Parts_Ann (Typ : Type_Kind_Id) return Boolean;
      --  Recursive function looking for access subcomponents

      -------------------------------
      -- Traverse_Access_Parts_Ann --
      -------------------------------

      function Traverse_Access_Parts_Ann (Typ : Type_Kind_Id) return Boolean is
         Rep_Ty : constant Type_Kind_Id := Retysp (Typ);
      begin
         if Is_Array_Type (Rep_Ty) then
            return Traverse_Access_Parts_Ann (Component_Type (Rep_Ty));

         elsif Is_Record_Type (Rep_Ty)
           or else Is_Incomplete_Or_Private_Type (Rep_Ty)
         then

            --  For tagged records, search only in the root type, extensions
            --  are not allowed to introduce deep components.

            if Is_Tagged_Type (Typ) and then Root_Retysp (Typ) /= Typ then
               return Traverse_Access_Parts_Ann (Root_Retysp (Typ));
            end if;

            if Has_Ownership_Annotation (Rep_Ty) then
               if Test (Rep_Ty) = Pass then
                  return True;
               end if;
            end if;

            if Is_Record_Type (Rep_Ty) then
               declare
                  Comp : Opt_E_Component_Id := First_Component (Rep_Ty);
               begin
                  while Present (Comp) loop
                     if Component_Is_Visible_In_SPARK (Comp)
                       and then Traverse_Access_Parts_Ann (Etype (Comp))
                     then
                        return True;
                     end if;
                     Next_Component (Comp);
                  end loop;
               end;
            end if;

            return False;

         elsif Is_Access_Type (Rep_Ty) then
            case Test (Rep_Ty) is
               when Fail =>
                  return False;
               when Pass =>
                  return True;
               when Continue =>
                  declare
                     Inserted : Boolean;
                     Position : Node_Sets.Cursor;
                     Des_Ty   : constant Type_Kind_Id :=
                       Directly_Designated_Type (Rep_Ty);
                  begin
                     Seen.Insert (Rep_Ty, Position, Inserted);

                     return not Inserted
                       or else Traverse_Access_Parts_Ann
                         (if Is_Incomplete_Type (Des_Ty)
                          then Full_View (Des_Ty)
                          else Des_Ty);
                  end;
            end case;
         else
            pragma Assert
              (Is_Scalar_Type (Rep_Ty)
               or else Is_Concurrent_Type (Rep_Ty));
            return False;
         end if;
      end Traverse_Access_Parts_Ann;

   --  Start of processing for Traverse_Access_Parts

   begin
      return Traverse_Access_Parts_Ann (Typ);
   end Traverse_Access_Parts;

   ---------------------------
   -- Have_Same_Known_Esize --
   ---------------------------

   procedure Have_Same_Known_Esize
     (A, B        :     Type_Kind_Id;
      Result      : out Boolean;
      Explanation : out Unbounded_String)
   is
   begin
      Check_Known_Esize (A, Result, Explanation);
      if not Result then
         return;
      end if;
      Check_Known_Esize (B, Result, Explanation);
      if not Result then
         return;
      end if;
      if Esize (A) /= Esize (B) then
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
   end Have_Same_Known_Esize;

   -----------------------------
   -- Have_Same_Known_RM_Size --
   -----------------------------

   procedure Have_Same_Known_RM_Size
     (A, B        :     Type_Kind_Id;
      Result      : out Boolean;
      Explanation : out Unbounded_String)
   is
   begin
      Check_Known_RM_Size (A, Result, Explanation);
      if not Result then
         return;
      end if;
      Check_Known_RM_Size (B, Result, Explanation);
      if not Result then
         return;
      end if;
      if RM_Size (A) /= RM_Size (B) then
         Result := False;
         Explanation :=
           To_Unbounded_String ("Size of " & Type_Name_For_Explanation (A)
                                & " and " & Type_Name_For_Explanation (B)
                                & " differ");
         return;
      end if;
      Result := True;
      Explanation := Null_Unbounded_String;
   end Have_Same_Known_RM_Size;

   -----------------------------
   -- Type_Is_Suitable_For_UC --
   -----------------------------

   function Type_Is_Suitable_For_UC
     (Typ       : Type_Kind_Id;
      Use_Esize : Boolean) return Result_Type
   is
      pragma Unreferenced (Use_Esize);
      function Typ_Name return String is (Type_Name_For_Explanation (Typ));

   begin
      --  We exclude types with discriminants and tags, private types, access
      --  types and concurrent types.

      if Is_Tagged_Type (Typ) then
         return
           (Ok          => False,
            Explanation =>
              To_Unbounded_String (Typ_Name & " is a tagged type"));
      end if;

      if Is_Incomplete_Or_Private_Type (Typ) then
         return
           (Ok          => False,
            Explanation =>
              To_Unbounded_String (Typ_Name & " is a private type"));
      end if;

      if Is_Concurrent_Type (Typ) then
         pragma Annotate
           (Xcov, Exempt_On, "The frontend crashes on UC on tasks and "
            & "rejectes UC on protected types");
         return
           (Ok          => False,
            Explanation =>
              To_Unbounded_String (Typ_Name & " is a concurrent type"));
         pragma Annotate (Xcov, Exempt_Off);
      end if;

      if Has_Discriminants (Typ) then
         return
           (Ok          => False,
            Explanation =>
              To_Unbounded_String (Typ_Name & " has discriminants"));
      end if;

      if Is_Access_Type (Typ) then
         return
           (Ok          => False,
            Explanation =>
              To_Unbounded_String (Typ_Name & " is an access type"));
      end if;

      return (Ok => True);
   end Type_Is_Suitable_For_UC;

   ------------------------------------
   -- Type_Is_Suitable_For_UC_Target --
   ------------------------------------

   function Type_Is_Suitable_For_UC_Target
     (Typ       : Type_Kind_Id;
      Use_Esize : Boolean) return Result_Type
   is
      function Typ_Name return String is (Type_Name_For_Explanation (Typ));

      Check_For_UC_Res : constant Result_Type :=
        Type_Is_Suitable_For_UC (Typ, Use_Esize);

   begin
      --  Return False if Typ is not "suitable for unchecked conversion"

      if not Check_For_UC_Res.Ok then
         return Check_For_UC_Res;
      end if;

      --  Some valid IEEE 754 values are not allowed in SPARK, such as NaN

      if Is_Floating_Point_Type (Typ) then
         return
           (Ok          => False,
            Explanation =>
              To_Unbounded_String ("floating-point types have invalid bit "
                & "patterns for SPARK"));
      end if;

      --  We exclude invariants and predicates

      if Invariant_Check_Needed (Typ)
        or else Has_Predicates (Typ)
      then
         return
           (Ok          => False,
            Explanation =>
              To_Unbounded_String
                (Typ_Name & " has invariants or predicates"));
      end if;

      --  Constrained scalar types are also excluded

      if Is_Scalar_Type (Typ) then
         declare
            R        : constant Node_Id := Scalar_Range (Typ);

            --  The size of scalar types is always known statically
            pragma Assert (Known_Esize (Typ) and Known_RM_Size (Typ));
            Typ_Size : constant Uint :=
              (if Use_Esize then Esize (Typ) else RM_Size (Typ));
         begin
               --  Despite having a known Esize, we might not know the bounds
               --  at compile time. Checking for this next.

            if not Compile_Time_Known_Value (Low_Bound (R)) then
               return
                 (Ok          => False,
                  Explanation =>
                    To_Unbounded_String ("lower bound for " & Typ_Name
                      & " is not known at compile time"));
            end if;

            if not Compile_Time_Known_Value (High_Bound (R)) then
               return
                 (Ok          => False,
                  Explanation =>
                    To_Unbounded_String ("upper bound for " & Typ_Name
                      & " is not known at compile time"));
            end if;

            declare
               Low        : constant Uint := Expr_Value (Low_Bound (R));
               High       : constant Uint := Expr_Value (High_Bound (R));
               Num_Values : constant Uint := High - Low + 1;
            begin
               if 2 ** Typ_Size = Num_Values then
                  return (Ok => True);
               else
                  return
                    (Ok          => False,
                     Explanation => To_Unbounded_String
                       (Typ_Name & " has "
                        & UI_Image (Num_Values)
                        & " values but has "
                        & (if Use_Esize then "Object_Size " else "Size ")
                        & UI_Image (Typ_Size)));
               end if;
            end;
         end;
      end if;

      return (Ok => True);
   end Type_Is_Suitable_For_UC_Target;

   -------------------------
   -- Unchecked_Full_Type --
   -------------------------

   function Unchecked_Full_Type (E : Type_Kind_Id) return Type_Kind_Id is
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

   function Use_Predefined_Equality_For_Type
     (Typ : Type_Kind_Id)
      return Boolean
   is
     (not (Is_Record_Type (Unchecked_Full_Type (Typ))
      or else Is_Limited_View (Typ))
      or else No (Get_User_Defined_Eq (Base_Type (Typ))));

   ----------------------------------
   -- Use_Real_Eq_For_Private_Type --
   ----------------------------------

   function Use_Real_Eq_For_Private_Type (E : Type_Kind_Id) return Boolean is

      function Use_Real_Eq_For_Type (E : Type_Kind_Id) return Boolean;
      --  Recursively traverse the type subcomponents and return False if
      --  a type is found which might make the equality on objects of type E
      --  imprecise.

      --------------------------
      -- Use_Real_Eq_For_Type --
      --------------------------

      function Use_Real_Eq_For_Type (E : Type_Kind_Id) return Boolean is
      begin
         case Ekind (E) is
            when Incomplete_Or_Private_Kind =>
               declare
                  Full_Type : constant Entity_Id := Unchecked_Full_Type (E);
               begin
                  return not Is_Incomplete_Or_Private_Type (Full_Type)
                    and then Use_Real_Eq_For_Type (Full_Type);
               end;

            when E_Record_Subtype
               | E_Record_Type
            =>
               --  The user defined equality of components of a record type
               --  will be used in the predefined equality of the enclosing
               --  composite type.

               if Present (Get_User_Defined_Eq (Base_Type (E))) then
                  return False;
               end if;

               --  Equality on tagged types ignores potential extensions

               if Is_Tagged_Type (E) then
                  return False;
               end if;

               declare
                  Comp : Entity_Id := First_Component_Or_Discriminant (E);
               begin
                  while Present (Comp) loop
                     if not Use_Real_Eq_For_Type (Etype (Comp)) then
                        return False;
                     end if;
                     Next_Component_Or_Discriminant (Comp);
                  end loop;
               end;
               return True;

            when Array_Kind =>

               --  Equality on unconstrained array types does not compare the
               --  bounds.

               return Is_Constrained (E)
                 and then Use_Real_Eq_For_Type (Component_Type (E));

            --  Equality on access types only returns True if the accesses
            --  are the same.

            when Access_Kind | Discrete_Kind | Fixed_Point_Kind =>
               return True;

            --  Equality on floating point type will return True on -0 and +0

            when Float_Kind =>
               return False;

            when others =>
               return False;
         end case;
      end Use_Real_Eq_For_Type;

   begin
      return Use_Real_Eq_For_Type (E);
   end Use_Real_Eq_For_Private_Type;

   ---------------------------------------
   -- Visible_Declarations_Of_Prot_Type --
   ---------------------------------------

   function Visible_Declarations_Of_Prot_Type
     (E : Protected_Kind_Id)
      return List_Id
   is (Visible_Declarations (Protected_Type_Definition (Base_Type (E))));

   ---------------------------------------
   -- Visible_Declarations_Of_Task_Type --
   ---------------------------------------

   function Visible_Declarations_Of_Task_Type
     (E : E_Task_Type_Id)
      return List_Id
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
