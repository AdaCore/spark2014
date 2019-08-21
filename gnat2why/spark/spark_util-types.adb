------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                        S P A R K _ U T I L - T Y P E S                   --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                     Copyright (C) 2016-2019, AdaCore                     --
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

with Elists;                     use Elists;
with Exp_Util;                   use Exp_Util;
with Sem_Eval;                   use Sem_Eval;
with SPARK_Annotate;             use SPARK_Annotate;
with SPARK_Definition;           use SPARK_Definition;
with SPARK_Util.Subprograms;     use SPARK_Util.Subprograms;

package body SPARK_Util.Types is

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

            elsif Is_Private_Type (Typ)
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

   begin
      return Has_Invariants_In_SPARK (Ty) and then
        Is_Declared_In_Main_Lib_Unit (Real_Node);
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

   -------------------------------
   -- Get_Initial_DIC_Procedure --
   -------------------------------

   function Get_Initial_DIC_Procedure (E : Entity_Id) return Entity_Id is
      Ty  : Entity_Id := Retysp (E);
      Anc : Entity_Id;

   begin
      --  If E has no DIC procedure, or if its DIC procedure has an associated
      --  body which has been marked, return it.

      if No (DIC_Procedure (E))
        or else (Present (Get_Body (DIC_Procedure (E)))
                 and then May_Need_DIC_Checking (E))
      then
         return DIC_Procedure (E);
      end if;

      --  An inherited DIC procedure may have no body. Go to the ancestor to
      --  find an adequate body.

      loop
         pragma Assert (Has_Inherited_DIC (Ty));
         Anc := Ty;
         if Full_View_Not_In_SPARK (Ty) then
            Ty := Get_First_Ancestor_In_SPARK (Ty);
         else
            Ty := Retysp (Etype (Ty));
         end if;

         pragma Assert (Present (DIC_Procedure (Ty)));

         exit when Anc = Ty
           or else (Present (Get_Body (DIC_Procedure (Ty)))
                    and then May_Need_DIC_Checking (Ty));
      end loop;

      if Present (Get_Body (DIC_Procedure (Ty)))
        and then May_Need_DIC_Checking (Ty)
      then
         return DIC_Procedure (Ty);

      --  The DIC has been inherited in a part not in SPARK. Ignore it.

      else
         pragma Assert (Full_View_Not_In_SPARK (Ty));
         return Empty;
      end if;
   end Get_Initial_DIC_Procedure;

   ---------------------------------
   -- Get_Iterable_Type_Primitive --
   ---------------------------------

   function Get_Iterable_Type_Primitive
     (Typ : Entity_Id;
      Nam : Name_Id) return Entity_Id
     is (Ultimate_Alias (Sem_Util.Get_Iterable_Type_Primitive (Typ, Nam)));

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
      Elmt    : Elmt_Id := First_Elmt (Discriminant_Constraint (Ty));
   begin
      while Current /= Discr loop
         Current := Next_Discriminant (Current);
         Elmt := Next_Elmt (Elmt);
      end loop;
      return Node (Elmt);
   end Get_Stored_Constraint_For_Discr;

   --------------------------------------
   -- Get_Type_With_Predicate_Function --
   --------------------------------------

   function Get_Type_With_Predicate_Function (E : Entity_Id) return Entity_Id
   is
     (if Present (Predicate_Function (E)) then E
      elsif Is_Itype (E) then Predicated_Parent (E)
      else Partial_View (E));

   -----------------------
   -- Has_Init_By_Proof --
   -----------------------

   function Has_Init_By_Proof (E : Entity_Id) return Boolean is
      Ty : constant Entity_Id := Retysp (E);
   begin
      case Type_Kind'(Ekind (Ty)) is
         when Scalar_Kind =>
            return Scalar_Has_Init_By_Proof (Ty);
         when Array_Kind =>
            return Has_Init_By_Proof (Component_Type (Ty));
         when Record_Kind =>

            --  A record type either has all its components with Init_By_Proof
            --  or none. Only check the first component that is visible in
            --  SPARK.

            declare
               Comp : Entity_Id :=
                 First_Component (Root_Retysp (Ty));
            begin
               while Present (Comp) loop
                  exit when Component_Is_Visible_In_SPARK (Comp);
                  Next_Component (Comp);
               end loop;

               return Present (Comp) and then Has_Init_By_Proof (Etype (Comp));
            end;
         when E_Private_Type
            | E_Private_Subtype
            | E_Limited_Private_Type
            | E_Limited_Private_Subtype
            | Concurrent_Kind
            | Access_Kind
          =>
            return False;

         when Incomplete_Kind
            | E_Exception_Type
            | E_Subprogram_Type
         =>
            raise Program_Error;
      end case;
   end Has_Init_By_Proof;

   -----------------------------
   -- Has_Invariants_In_SPARK --
   -----------------------------

   function Has_Invariants_In_SPARK (E : Entity_Id) return Boolean is
     (Has_Own_Invariants (E)
      and then Ekind (E) not in Subtype_Kind
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

   -------------------
   -- Is_Null_Range --
   -------------------

   function Is_Null_Range (T : Entity_Id) return Boolean is
     (Is_Discrete_Type (T)
      and then Has_Static_Scalar_Subtype (T)
      and then Expr_Value (Low_Bound (Scalar_Range (T))) >
          Expr_Value (High_Bound (Scalar_Range (T))));

   ----------------------
   -- Is_Standard_Type --
   ----------------------

   function Is_Standard_Type (E : Entity_Id) return Boolean is
     (for some S_Type in S_Types => Standard_Entity (S_Type) = E);

   ------------------------------
   -- Is_Standard_Boolean_Type --
   ------------------------------

   function Is_Standard_Boolean_Type (E : Entity_Id) return Boolean is
     (E = Standard_Boolean
      or else
        (Ekind (E) = E_Enumeration_Subtype
         and then Etype (E) = Standard_Boolean
         and then Scalar_Range (E) = Scalar_Range (Standard_Boolean)
         and then not Has_Predicates (E)
         and then not Scalar_Has_Init_By_Proof (E)));

   --------------------------
   -- Is_Static_Array_Type --
   --------------------------

   function Is_Static_Array_Type (E : Entity_Id) return Boolean is
     (Is_Array_Type (E)
        and then Is_Constrained (E)
        and then Has_Static_Array_Bounds (E));

   ---------------------------
   -- May_Need_DIC_Checking --
   ---------------------------

   function May_Need_DIC_Checking (E : Entity_Id) return Boolean is
      DIC_Needs_To_Be_Checked : constant Boolean :=
        Has_Own_DIC (E)
        and then Present (DIC_Procedure (E));

      DIC_Needs_To_Be_Rechecked : constant Boolean :=
        Is_Tagged_Type (E)
        and then Is_Full_View (E)
        and then Present (DIC_Procedure (E))
        and then Expression_Contains_Primitives_Calls_Of
          (Get_Expr_From_Check_Only_Proc (DIC_Procedure (E)), E);
   begin
      return DIC_Needs_To_Be_Checked or DIC_Needs_To_Be_Rechecked;
   end May_Need_DIC_Checking;

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
