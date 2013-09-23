------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                            S P A R K _ U T I L                           --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                        Copyright (C) 2011-2013, AdaCore                  --
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

with Fname;    use Fname;
with Lib;      use Lib;
with Nlists;   use Nlists;
with Sem_Util; use Sem_Util;
with Sinput;   use Sinput;
with Treepr;   use Treepr;
with Uintp;    use Uintp;

package body SPARK_Util is
   ------------------
   -- Global State --
   ------------------

   Full_To_Partial_Entities : Node_Maps.Map;
   --  Map from full views of entities to their partial views, for deferred
   --  constants and private types.

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

      procedure Skip_Generated_Components (Component : in out Entity_Id);
      --  If Component is a compiler generated component, skip it and the
      --  following compiler generated components, until a component coming
      --  from source is reached. Otherwise, set Component to Empty.

      -------------------------------
      -- Skip_Generated_Components --
      -------------------------------

      procedure Skip_Generated_Components (Component : in out Entity_Id) is
      begin
         while Present (Component)
           and then not Comes_From_Source (Component)
         loop
            Component := Next_Component_Or_Discriminant (Component);
         end loop;
      end Skip_Generated_Components;

      Typ         : constant Entity_Id := Underlying_Type (Etype (N));
      Assocs      : List_Id;
      Component   : Entity_Id;
      Association : Node_Id;

   --  Start of Aggregate_Is_Fully_Initialized

   begin
      if Is_Record_Type (Typ) then
         pragma Assert (Is_Empty_List (Expressions (N)));

         Assocs      := Component_Associations (N);
         Component   := First_Component_Or_Discriminant (Typ);
         Association := First (Assocs);

         Skip_Generated_Components (Component);

         while Present (Component) loop
            if Present (Association)
              and then Matching_Component_Association (Component, Association)
            then
               if Box_Present (Association) then
                  return False;
               end if;
               Next (Association);
            else
               return False;
            end if;

            Component := Next_Component_Or_Discriminant (Component);
            Skip_Generated_Components (Component);
         end loop;

      else
         pragma Assert (Is_Array_Type (Typ) or else Is_String_Type (Typ));

         Assocs := Component_Associations (N);

         if Present (Assocs) then
            Association := First (Assocs);

            while Present (Association) loop
               if Box_Present (Association) then
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

   ------------
   -- Append --
   ------------

   procedure Append
     (To    : in out List_Of_Nodes.List;
      Elmts : List_Of_Nodes.List) is
   begin
      for E of Elmts loop
         To.Append (E);
      end loop;
   end Append;

   procedure Append
     (To    : in out Node_Lists.List;
      Elmts : Node_Lists.List) is
   begin
      for E of Elmts loop
         To.Append (E);
      end loop;
   end Append;

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
      end if;

      return True;
   end Check_Needed_On_Conversion;

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
     (Stmts : List_Id) return List_Of_Nodes.List
   is
      Cur_Stmt   : Node_Id := Nlists.First (Stmts);
      Flat_Stmts : List_Of_Nodes.List;

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

   function Get_Formal_Type_From_Actual (Actual : Node_Id) return Entity_Id is
      Formal_Type : Entity_Id := Empty;

      procedure Check_Call_Arg (Some_Formal, Some_Actual : Node_Id);
      --  If Some_Actual is the desired actual parameter, set Formal_Type to
      --  the type of the corresponding formal parameter.

      --------------------
      -- Check_Call_Arg --
      --------------------

      procedure Check_Call_Arg (Some_Formal, Some_Actual : Node_Id) is
      begin
         if Some_Actual = Actual then
            Formal_Type := Etype (Some_Formal);
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

      pragma Assert (Present (Formal_Type));

      return Formal_Type;
   end Get_Formal_Type_From_Actual;

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
        Expressions (Expression (PAA)) /= No_List then
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
        Component_Associations (Expression (PAA)) /= No_List then
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

   ----------------------------------------
   -- Get_Statement_And_Declaration_List --
   ----------------------------------------

   function Get_Statement_And_Declaration_List
     (Stmts : List_Id) return List_Of_Nodes.List
   is
      Cur_Stmt   : Node_Id := Nlists.First (Stmts);
      New_Stmts : List_Of_Nodes.List;

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
      Prag : Node_Id := Contract_Test_Cases (Contract (E));
   begin
      while Present (Prag) loop
         if Pragma_Name (Prag) = Name_Contract_Cases then
            return Prag;
         end if;
         Prag := Next_Pragma (Prag);
      end loop;
      return Empty;
   end Get_Subprogram_Contract_Cases;

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

   -----------------------------------------------------
   -- Has_Annotate_Pragma_For_External_Axiomatization --
   -----------------------------------------------------

   function Has_Annotate_Pragma_For_External_Axiomatization
     (E : Entity_Id) return Boolean
   is
      Decl      : constant Node_Id := Get_Package_Spec (E);
      Vis_Decls : constant List_Id := Visible_Declarations (Decl);
      N         : Node_Id;

   begin
      N := First (Vis_Decls);
      while Present (N) loop

         --  Skip declarations generated by the frontend. Skip all pragmas that
         --  are not the desired Annotate pragma. Stop the search on the first
         --  non-pragma source declaration.

         if Comes_From_Source (N) then
            if Nkind (N) = N_Pragma then
               if Is_Annotate_Pragma_For_External_Axiomatization (N) then
                  return True;
               end if;
            else
               return False;
            end if;
         end if;

         Next (N);
      end loop;

      return False;
   end Has_Annotate_Pragma_For_External_Axiomatization;

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
      Cur    : Node_Id := N;
      Result : Node_Id := Empty;

   begin
      while Present (Cur) loop
         if Nkind (Cur) = N_Loop_Statement then
            Result := Cur;

         --  Prevent the search from going too far

         elsif Nkind_In (Cur, N_Entry_Body,
                              N_Package_Body,
                              N_Package_Declaration,
                              N_Protected_Body,
                              N_Subprogram_Body,
                              N_Task_Body)
         then
            exit;
         end if;

         Cur := Parent (Cur);
      end loop;

      return Result;
   end Innermost_Enclosing_Loop;

   ----------------------------------------------------
   -- Is_Annotate_Pragma_For_External_Axiomatization --
   ----------------------------------------------------

   --  The general form of pragma Annotate is

   --    pragma Annotate (IDENTIFIER [, IDENTIFIER {, ARG}]);
   --    ARG ::= NAME | EXPRESSION

   --  The first two arguments are by convention intended to refer to an
   --  external tool and a tool-specific function. These arguments are
   --  not analyzed.

   --  The following is used to annotate a package specification which
   --  GNATprove should treat specially, because the axiomatization of
   --  this unit is given by the user instead of being automatically generated.

   --    pragma Annotate (GNATprove, External_Axiomatization);

   function Is_Annotate_Pragma_For_External_Axiomatization
     (N : Node_Id) return Boolean is
   begin
      if Nkind (N) = N_Pragma
        and then Get_Pragma_Id (Pragma_Name (N)) = Pragma_Annotate
        and then List_Length (Pragma_Argument_Associations (N)) = 2
      then
         declare
            Arg1 : constant Node_Id :=
              First (Pragma_Argument_Associations (N));
            Arg2 : constant Node_Id := Next (Arg1);
            Nam1 : Name_Id;
            Nam2 : Name_Id;
         begin
            --  Fill in Name_Buffer with Name_GNATprove first, and then with
            --  Name_External_Axiomatization so that Name_Find returns the
            --  corresponding name. This takes care of all possible casings.

            Name_Len := 0;
            Add_Str_To_Name_Buffer (Name_GNATprove);
            Nam1 := Name_Find;

            Name_Len := 0;
            Add_Str_To_Name_Buffer (Name_External_Axiomatization);
            Nam2 := Name_Find;

            return Chars (Get_Pragma_Arg (Arg1)) = Nam1
                     and then
                   Chars (Get_Pragma_Arg (Arg2)) = Nam2;
         end;

      else
         return False;
      end if;
   end Is_Annotate_Pragma_For_External_Axiomatization;

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

   ------------------
   -- Is_Full_View --
   ------------------

   function Is_Full_View (E : Entity_Id) return Boolean is
      (Full_To_Partial_Entities.Contains (E));

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

   ---------------------------------
   -- Package_Has_External_Axioms --
   ---------------------------------

   function Package_Has_External_Axioms (E : Entity_Id) return Boolean
   is
   begin
      return Has_Annotate_Pragma_For_External_Axiomatization (E);
   end Package_Has_External_Axioms;

   -------------------------------
   -- Entity_In_External_Axioms --
   -------------------------------

   function Entity_In_External_Axioms (E : Entity_Id) return Boolean is
   begin
      if Present (E) then
         if Ekind (E) = E_Package and then
           Package_Has_External_Axioms (E) then
            return True;
         end if;
         if Entity_In_External_Axioms (Scope (E)) then
            return True;
         else
            return Ekind (E) = E_Package and then
              Entity_In_External_Axioms
                (Generic_Parent (Get_Package_Spec (E)));
         end if;
      else
         return False;
      end if;
   end Entity_In_External_Axioms;

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

   -------------------------------------
   -- Is_External_Axioms_Discriminant --
   -------------------------------------

   function Is_External_Axioms_Discriminant (E : Entity_Id) return Boolean is
      Typ : constant Entity_Id :=
        Most_Underlying_Type
          (Unique_Defining_Entity (Get_Enclosing_Declaration (E)));
   begin
      return Entity_In_External_Axioms (Typ);
   end Is_External_Axioms_Discriminant;

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

   ---------------------
   -- Is_Pragma_Check --
   ---------------------

   function Is_Pragma_Check (N : Node_Id; Name : Name_Id) return Boolean is
     (Is_Pragma (N, Pragma_Check)
        and then
      Chars (Get_Pragma_Arg (First (Pragma_Argument_Associations (N))))
      = Name);

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

   --------------------------
   -- Most_Underlying_Type --
   --------------------------

   function Most_Underlying_Type (E : Entity_Id) return Entity_Id is
      Typ : Entity_Id := E;
   begin
      loop
         --  For types in packages with external axioms, do not consider the
         --  underlying type.

         if Entity_In_External_Axioms (Typ) then
            return Typ;
         elsif Ekind (Typ) in Private_Kind then
            Typ := Underlying_Type (Typ);
         else
            return Typ;
         end if;
      end loop;
   end Most_Underlying_Type;

   -----------------------
   -- Number_Components --
   -----------------------

   function Number_Components (Typ : Entity_Id) return Natural is
      Count     : Natural := 0;
      Component : Entity_Id := First_Component_Or_Discriminant (Typ);
   begin
      while Component /= Empty loop
         Count := Count + 1;
         Component := Next_Component_Or_Discriminant (Component);
      end loop;
      return Count;
   end Number_Components;

   ------------------
   -- Partial_View --
   ------------------

   function Partial_View (E : Entity_Id) return Entity_Id is
      (Full_To_Partial_Entities.Element (E));

   ---------------------------
   -- Root_Record_Component --
   ---------------------------

   function Root_Record_Component (E : Entity_Id) return Entity_Id is

      Rec_Type : constant Entity_Id := Unique_Entity (Scope (E));
      Root     : constant Entity_Id := Root_Record_Type (Rec_Type);

   --  Start of Root_Record_Component

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
      Result : Entity_Id := E;

   begin
      --  Climb the type derivation chain with Root_Type, applying
      --  Underlying_Type to pass private type boundaries.

      while Underlying_Type (Root_Type (Result)) /= Result loop
         Result := Underlying_Type (Root_Type (Result));
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
      Cur_Comp : Entity_Id := First_Component_Or_Discriminant (Rec);

   begin
      while Present (Cur_Comp) loop
         if Chars (Cur_Comp) = Chars (Comp) then
            return Cur_Comp;
         end if;

         Next_Component_Or_Discriminant (Cur_Comp);
      end loop;

      --  We *must* find a component, so we should never be here
      raise Program_Error;
   end Search_Component_By_Name;

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
      Typ : Entity_Id := E;
   begin
      loop
         if Entity_In_External_Axioms (Typ) then
            return Typ;
         elsif Ekind (Typ) in Private_Kind then
            Typ := Underlying_Type (Typ);
         elsif Ekind (Typ) in Record_Kind then
            if Typ = Etype (Typ) or else
              Underlying_Type (Etype (Typ)) = Typ then
               return Empty;
            end if;
            Typ := Etype (Typ);
         else
            return Empty;
         end if;
      end loop;
   end Underlying_External_Axioms_Type;

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

end SPARK_Util;
