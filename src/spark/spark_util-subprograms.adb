------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                  S P A R K _ U T I L - S U B P R O G R A M S             --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                     Copyright (C) 2016-2020, AdaCore                     --
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

with Ada.Strings.Equal_Case_Insensitive;
with Ada.Strings;                        use Ada.Strings;
with Common_Iterators;                   use Common_Iterators;
with Debug;
with Flow_Dependency_Maps;               use Flow_Dependency_Maps;
with Flow_Generated_Globals.Phase_2;     use Flow_Generated_Globals.Phase_2;
with Flow_Refinement;                    use Flow_Refinement;
with Flow_Types;                         use Flow_Types;
with Flow_Utility;                       use Flow_Utility;
with GNATCOLL.Utils;                     use GNATCOLL.Utils;
with Rtsfind;                            use Rtsfind;
with Sem_Ch12;                           use Sem_Ch12;
with Sem_Prag;                           use Sem_Prag;
with SPARK_Definition;                   use SPARK_Definition;
with SPARK_Definition.Annotate;          use SPARK_Definition.Annotate;
with SPARK_Util.Types;                   use SPARK_Util.Types;
with Stand;                              use Stand;
with VC_Kinds;                           use VC_Kinds;

package body SPARK_Util.Subprograms is

   ------------------------
   -- Analysis_Requested --
   ------------------------

   function Analysis_Requested
     (E            : Entity_Id;
      With_Inlined : Boolean) return Analysis_Status is
   begin
      --  Either the analysis is requested for the complete unit, or if it is
      --  requested for a specific subprogram/task, check whether it is E.

      if not Is_In_Analyzed_Files (E) then
         return Not_In_Analyzed_Files;

      --  Always analyze the subprogram if analysis was specifically requested
      --  for it, and not other subprograms in that case.

      elsif Is_Requested_Subprogram_Or_Task (E) then
         return Analyzed;

      elsif Gnat2Why_Args.Limit_Subp /= Null_Unbounded_String then
         return Not_The_Analyzed_Subprogram;

      --  Always analyze if With_Inlined is True. Also, always analyze
      --  unreferenced subprograms, as they are likely to correspond to
      --  an intermediate stage of development. Otherwise, only analyze
      --  subprograms that are not inlined.

      elsif With_Inlined then
         return Analyzed;

      elsif not Referenced (E) then
         return Analyzed;

      elsif Is_Local_Subprogram_Always_Inlined (E) then
         return Contextually_Analyzed;

      else
         return Analyzed;
      end if;
   end Analysis_Requested;

   ------------------------------
   -- Call_Needs_Variant_Check --
   ------------------------------

   function Call_Needs_Variant_Check
     (Call : Node_Id; Enclosing_Ent : Entity_Id) return Boolean
   is
      Called         : constant Entity_Id :=
        (if Nkind (Call) in N_Op then Entity (Call)
         else Get_Called_Entity (Call));
      Enclosing_Subp : Entity_Id := Enclosing_Ent;

   begin
      if not Is_Subprogram_Or_Entry (Called)
        or else not Flow_Generated_Globals.Phase_2.Is_Recursive (Called)
      then
         return False;

      --  Go up the scope to search for a subprogram or entry. Theoretically,
      --  we could stop as soon as we encounter something which is not a
      --  package, as indirect recursive calls inside types are not allowed.
      --  Still, since this is not enforced currently, it seems better to
      --  continue climbing the scope chain.

      else
         while Present (Enclosing_Subp) loop

            --  We have found a subprogram, check whether it is mutually
            --  recursive with Called.  If it is, return True if either
            --  Enclosing_Subp or Called has a variant.
            --  If one has a variant and not the other, we will emit a
            --  statically False check.

            if Is_Subprogram_Or_Entry (Enclosing_Subp) then
               return Flow_Generated_Globals.Phase_2.Mutually_Recursive
                 (Enclosing_Subp, Called)
                 and then
                   (Present
                      (Get_Pragma (Enclosing_Subp, Pragma_Subprogram_Variant))
                    or else
                     Present (Get_Pragma (Called, Pragma_Subprogram_Variant)));

            --  Concurrent types should be declared at library level

            elsif Is_Concurrent_Type (Enclosing_Subp) then
               return False;
            else
               Enclosing_Subp := Scope (Enclosing_Subp);
            end if;
         end loop;

         return False;
      end if;
   end Call_Needs_Variant_Check;

   -------------------------
   -- Compatible_Variants --
   -------------------------

   function Compatible_Variants (E1, E2 : Entity_Id) return Boolean is
      Variants1 : constant Node_Id :=
        Get_Pragma (E1, Pragma_Subprogram_Variant);
      Variants2 : constant Node_Id :=
        Get_Pragma (E2, Pragma_Subprogram_Variant);

   begin
      --  Return True if both E1 and E2 have variants supplied, and all their
      --  variants have the same mode and the same base type.
      --  ??? In the RFC, we discussed allowing either E1 or E2 to have less
      --  variants than the other. This is not implemented yet.

      if No (Variants1) or else No (Variants2) then
         return False;
      elsif E1 = E2 then
         return True;
      else
         declare
            Aggr1 : constant Node_Id :=
              Expression (First (Pragma_Argument_Associations (Variants1)));
            Variant1 : Node_Id := First (Component_Associations (Aggr1));
            Aggr2    : constant Node_Id :=
              Expression (First (Pragma_Argument_Associations (Variants2)));
            Variant2 : Node_Id := First (Component_Associations (Aggr2));
         begin
            while Present (Variant1) loop
               if No (Variant2)
                 or else Chars (First (Choices (Variant1))) /=
                   Chars (First (Choices (Variant2)))
                 or else
                   Unique_Entity (Base_Type (Etype (Expression (Variant1)))) /=
                   Unique_Entity (Base_Type (Etype (Expression (Variant2))))
               then
                  return False;
               end if;
               Next (Variant1);
               Next (Variant2);
            end loop;

            return No (Variant2);
         end;
      end if;
   end Compatible_Variants;

   -------------------------------
   -- Containing_Protected_Type --
   -------------------------------

   function Containing_Protected_Type (E : Entity_Id) return Entity_Id is
      Scop : Node_Id := Scope (E);
   begin
      while Present (Scop) loop
         if Is_Protected_Type (Scop) then
            return Scop;
         end if;
         Scop := Scope (Scop);
      end loop;

      --  should not reach this - we should be in the scope of a protected type

      raise Program_Error;

   end Containing_Protected_Type;

   -----------------------------
   -- Corresponding_Primitive --
   -----------------------------

   function Corresponding_Primitive (Subp, Ty : Entity_Id) return Entity_Id is
   begin
      for Prim of Iter (Direct_Primitive_Operations (Ty)) loop
         declare
            Ty_S    : constant Entity_Id := Ultimate_Alias (Prim);
            Current : Entity_Id := Ty_S;
         begin
            loop
               if Current = Subp then
                  return Ty_S;
               end if;
               Current := Overridden_Operation (Current);
               exit when No (Current);
               Current := Ultimate_Alias (Current);
            end loop;
         end;
      end loop;
      raise Program_Error;
   end Corresponding_Primitive;

   --------------------------
   -- Enclosing_Subprogram --
   --------------------------

   function Enclosing_Subprogram (E : Entity_Id) return Entity_Id is
      Context : Entity_Id := E;
   begin
      while Ekind (Context) in E_Package | E_Block loop
         Context := Scope (Context);
      end loop;
      return Context;
   end Enclosing_Subprogram;

   ----------------
   -- Entry_Body --
   ----------------

   function Entry_Body (E : Entity_Id) return Node_Id
   is
      Ptr : constant Node_Id := Entry_Body_Entity (E);
   begin
      return (if Present (Ptr)
              then Parent (Ptr)
              else Empty);
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

   -------------------
   -- Find_Contract --
   -------------------

   function Find_Contract (E : Entity_Id; Prag : Pragma_Id) return Node_Id is
   begin
      case Prag is
         when Pragma_Global
            | Pragma_Depends
         =>
            return Get_Pragma ((if Ekind (E) = E_Task_Type
                                  and then Is_Single_Concurrent_Type (E)
                                then Anonymous_Object (E)
                                else E),
                               Prag);

         when Pragma_Refined_Global
            | Pragma_Refined_Depends
         =>
            declare
               Body_N : constant Node_Id := Get_Body (E);
            begin
               if Present (Body_N) then
                  --  Refined contracts on separate subprograms are attached to
                  --  the stub entity (which is neither the unique entity nor
                  --  the body entity). Detect these by checking whether the
                  --  body defintion is in a subunit.

                  declare
                     Context : constant Node_Id := Parent (Body_N);

                     pragma Assert
                       (Nkind (Context) in N_Subunit
                                         | N_Block_Statement
                                         | N_Compilation_Unit
                                         | N_Entry_Body
                                         | N_Protected_Body
                                         | N_Package_Body
                                         | N_Package_Specification
                                         | N_Subprogram_Body
                                         | N_Task_Body);

                  begin
                     return
                       Get_Pragma
                         (Defining_Entity
                            (if Nkind (Context) = N_Subunit
                             then Corresponding_Stub (Context)
                             else Body_N),
                          Prag);
                  end;
               else
                  return Empty;
               end if;
            end;

         when others =>
            raise Program_Error;
      end case;
   end Find_Contract;

   --------------------
   -- Find_Contracts --
   --------------------

   function Find_Contracts
     (E         : Entity_Id;
      Name      : Pragma_Id;
      Classwide : Boolean := False;
      Inherited : Boolean := False) return Node_Lists.List
   is
      function Filter_Classwide_Contracts
        (Pragmas : Node_Lists.List;
         From    : Entity_Id) return Node_Lists.List;
      --  Return the contracts from Contracts that are inherited from From

      --------------------------------
      -- Filter_Classwide_Contracts --
      --------------------------------

      function Filter_Classwide_Contracts
        (Pragmas : Node_Lists.List;
         From    : Entity_Id) return Node_Lists.List
      is
         Result : Node_Lists.List;
      begin
         for Prag of Pragmas loop
            if From_Aspect_Specification (Prag)
              and then Entity (Corresponding_Aspect (Prag)) = From
            then
               Result.Append (Prag);
            end if;
         end loop;
         return Result;
      end Filter_Classwide_Contracts;

      --  Local variables

      Contr   : Node_Id;
      Prag    : Node_Id;
      Pragmas : Node_Lists.List := Node_Lists.Empty_List;

      Class_Expected : constant Boolean := Classwide or Inherited;
      --  True iff the Class flag should be set on selected pragmas

   --  Start of processing for Find_Contracts

   begin
      case Name is
         when Pragma_Precondition
            | Pragma_Postcondition
            | Pragma_Refined_Post
            | Pragma_Initial_Condition
         =>
            if Name = Pragma_Refined_Post then

               --  Querying the Refined_Post is only allowed when the body is
               --  annotated with SPARK_Mode => On; otherwise, GNATprove must
               --  make no decision based on the presence, absence or contents
               --  of this contract.

               pragma Assert (Entity_Body_In_SPARK (E));

               declare
                  Body_E : constant Entity_Id := Get_Body_Entity (E);
                  --  ??? here we shall check for stubs, just like we do in
                  --  Find_Contracts above.
               begin
                  Contr := (if Present (Body_E)
                            then Contract (Body_E)
                            else Empty);
               end;

            else
               Contr := Contract (E);
            end if;

            if Present (Contr) then
               Prag :=
                 (case Name is
                     when Pragma_Precondition  |
                          Pragma_Postcondition |
                          Pragma_Refined_Post  =>
                        Pre_Post_Conditions (Contr),

                     when Pragma_Initial_Condition =>
                        Classifications (Contr),

                     when others =>
                        raise Program_Error);

               while Present (Prag) loop
                  if Get_Pragma_Id (Prag) = Name
                    and then Class_Present (Prag) = Class_Expected
                  then
                     Pragmas.Append (Prag);
                  end if;

                  Prag := Next_Pragma (Prag);
               end loop;
            end if;

         when others =>
            raise Program_Error;
      end case;

      --  If Inherited is True, look for an inherited contract, starting from
      --  the closest overridden subprogram.

      --  ??? Does not work for multiple inheritance through interfaces

      if Classwide then
         Pragmas := Filter_Classwide_Contracts (Pragmas, E);

      elsif Inherited then
         declare
            Inherit_Subp : constant Subprogram_List :=
              Inherited_Subprograms (E);
            Inherit_Pragmas : Node_Lists.List;
         begin
            for J in Inherit_Subp'Range loop
               Inherit_Pragmas :=
                 Filter_Classwide_Contracts
                   (Pragmas, Ultimate_Alias (Inherit_Subp (J)));
               exit when not Inherit_Pragmas.Is_Empty;
            end loop;
            Pragmas := Inherit_Pragmas;
         end;
      end if;

      --  Extract the Boolean expressions inside the pragmas, and return the
      --  list of these expressions.

      declare
         Contracts : Node_Lists.List;
      begin
         for P of Pragmas loop
            Contracts.Append
              (Expression (First (Pragma_Argument_Associations (P))));
         end loop;

         return Contracts;
      end;
   end Find_Contracts;

   --------------------------------
   -- Find_Dispatching_Parameter --
   --------------------------------

   function Find_Dispatching_Parameter (E : Entity_Id) return Entity_Id is
      Formal : Entity_Id := First_Formal (E);

   begin
      while Present (Formal) loop
         if Is_Controlling_Formal (Formal) then
            return Formal;
         end if;

         Next_Formal (Formal);
      end loop;

      raise Program_Error;
   end Find_Dispatching_Parameter;

   ---------------------------
   -- Find_Dispatching_Type --
   ---------------------------

   function Find_Dispatching_Type (E : Entity_Id) return Entity_Id is
      Subp   : constant Entity_Id := Ultimate_Alias (E);
      Formal : Entity_Id;
      D_Type : Entity_Id := Empty;

   begin
      --  Dispatching calls to invisible dispatching opearations are not
      --  allowed in SPARK.

      if Is_Invisible_Dispatching_Operation (E) then
         return Empty;
      end if;

      --  If E has a controlling result, the dispatching type is the result
      --  type.

      if Ekind (Subp) = E_Function
        and then Has_Controlling_Result (Subp)
      then
         D_Type := Retysp (Etype (E));

      --  Otherwise, find a controling formal. There should always be one.

      else
         Formal := First_Formal (Subp);

         loop
            pragma Assert (Present (Formal));
            if Is_Controlling_Formal (Formal) then
               D_Type := Retysp (Etype (Formal));
               exit;
            end if;

            Next_Formal (Formal);
         end loop;

         pragma Assert (Present (D_Type));

         --  Formal parameters of unconstrained types will have the first
         --  subtypes as Etypes, return their base type instead.

         if Is_First_Subtype (D_Type) then
            D_Type := Base_Retysp (D_Type);
         end if;
      end if;

      --  It can happen that D_Type is not tagged even if E is not a public
      --  subprogram (Is_Invisible_Dispatching_Operation returns False). In
      --  that case, E should not be considered dispatching in SPARK.

      if Is_Tagged_Type (D_Type) then
         return D_Type;
      else
         return Empty;
      end if;
   end Find_Dispatching_Type;

   ------------------------
   -- Get_Execution_Kind --
   ------------------------

   function Get_Execution_Kind
     (E        : Entity_Id;
      After_GG : Boolean := True) return Execution_Kind_T
   is
      function Has_Output return Boolean;
      --  Return True either when procedure E has output (parameter or global)
      --  or when don't know for sure (because no Global has been generated
      --  yet). If After_GG is False, then we will not query generated globals.

      ----------------
      -- Has_Output --
      ----------------

      function Has_Output return Boolean is
         Formal : Entity_Id := First_Formal (E);

         Globals : Global_Flow_Ids;

      begin
         --  Consider output parameters

         while Present (Formal) loop
            case Formal_Kind'(Ekind (Formal)) is
               when E_Out_Parameter
                  | E_In_Out_Parameter
               =>
                  return True;
               when E_In_Parameter =>
                  null;
            end case;
            Next_Formal (Formal);
         end loop;

         --  Consider output globals if they can be relied upon, either because
         --  this is after the generation of globals, or because the user has
         --  supplied them.

         if After_GG or else Has_User_Supplied_Globals (E) then
            Get_Globals (Subprogram          => E,
                         Scope               => Get_Flow_Scope (E),
                         Classwide           => True,
                         Globals             => Globals,
                         Use_Deduced_Globals => After_GG);

            return not Globals.Outputs.Is_Empty;

         --  Otherwise we don't know, return True to be on the safe side

         else
            return True;
         end if;
      end Has_Output;

   --  Start of processing for Get_Execution_Kind

   begin
      return (if Has_Output
              then Infinite_Loop
              else Abnormal_Termination);
   end Get_Execution_Kind;

   -----------------------------------
   -- Get_Expr_From_Check_Only_Proc --
   -----------------------------------

   function Get_Expr_From_Check_Only_Proc (E : Entity_Id) return Node_Id is
      Body_N : constant Node_Id := Subprogram_Body (E);
      Stmt   : Node_Id;
      Arg    : Node_Id;

   begin
      --  If there is no associated body, return Empty

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
            return Get_Pragma_Arg (Arg);
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

      --  Get the original node either from the declaration for E, or from the
      --  subprogram body for E, which may be different if E is attached to a
      --  subprogram declaration.

   begin
      return
        Original_Node
          (if Is_Rewrite_Substitution (Decl_N)
           then Decl_N
           else Subprogram_Body (E));
   end Get_Expression_Function;

   ----------------------------------------
   -- Get_Priority_Or_Interrupt_Priority --
   ----------------------------------------

   function Get_Priority_Or_Interrupt_Priority (E : Entity_Id) return Node_Id
   is
      Priority_Node : constant Node_Id := Get_Rep_Item (E, Name_Priority);
      --  Note that the above will also find Name_Interrupt_Priority (see
      --  comment on Get_Rep_Item).
   begin
      if Present (Priority_Node) then
         case Nkind (Priority_Node) is
            when N_Pragma =>
               declare
                  Arg : constant Node_Id :=
                    First (Pragma_Argument_Associations (Priority_Node));

               begin
                  return (if Present (Arg)
                          then Expression (Arg)
                          --  Here priority defaults to
                          --  Interrupt_Priority'Last.
                          else Empty);
               end;

            when N_Attribute_Definition_Clause =>
               return Expression (Priority_Node);

            when others =>
               raise Program_Error;
         end case;

      else
         return Empty;
      end if;
   end Get_Priority_Or_Interrupt_Priority;

   ---------------------------
   -- Includes_Current_Task --
   ---------------------------

   function Includes_Current_Task (Calls : Node_Sets.Set) return Boolean is
      (for some Call of Calls => Is_RTE (Call, RE_Current_Task));

   -------------------
   -- Has_Contracts --
   -------------------

   function Has_Contracts
     (E         : Entity_Id;
      Name      : Pragma_Id;
      Classwide : Boolean := False;
      Inherited : Boolean := False) return Boolean
   is
   begin
      --  If classwide or inherited is specified then check only there

      if Classwide or Inherited then
         if Classwide
           and then not Find_Contracts (E, Name, Classwide => True).Is_Empty
         then
            return True;
         end if;

         return Inherited
           and then not Find_Contracts (E, Name, Inherited => True).Is_Empty;

      --  Otherwise check the ordinary contract

      else
         return not Find_Contracts (E, Name).Is_Empty;
      end if;
   end Has_Contracts;

   ----------------------------
   -- Has_Extensions_Visible --
   ----------------------------

   function Has_Extensions_Visible (E : Entity_Id) return Boolean is
     (Present (Get_Pragma (E, Pragma_Extensions_Visible)));

   ----------------------------
   -- Has_Subprogram_Variant --
   ----------------------------

   function Has_Subprogram_Variant (E : Entity_Id) return Boolean is
      (Present (Get_Pragma (E, Pragma_Subprogram_Variant)));

   -------------------------------
   -- Has_User_Supplied_Globals --
   -------------------------------

   function Has_User_Supplied_Globals (E : Entity_Id) return Boolean is
     (Present (Find_Contract (E, Pragma_Global))
        or else
      Present (Find_Contract (E, Pragma_Depends))
        or else
      Is_Pure (E));

   ----------------------------------------
   -- Is_Possibly_Nonreturning_Procedure --
   ----------------------------------------

   function Is_Possibly_Nonreturning_Procedure (E : Entity_Id) return Boolean
   is
     (No_Return (E)
       or else
      Has_Might_Not_Return_Annotation (E));

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
      --    Ada.Strings.[[Wide_]Wide_]Unbounded.[[Wide_]Wide_]Text_IO
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
      --  and use a circular buffer instead.

      Max_Predefined_Potentially_Blocking_Nesting : constant := 5;
      --  Maximal nesting of predefined potentially blocking subprograms

      type Scope_Index is mod Max_Predefined_Potentially_Blocking_Nesting;
      --  Modular type for indexing the circular buffer

      Scopes : array (Scope_Index) of Entity_Id;
      --  Circular buffer with scopes of a call

      Scope_Id : Scope_Index := Scope_Index'Last;
      --  Indexing variable

      function Scope_Name (Nth : Scope_Index) return Name_Id with
        Pure_Function;
      --  Return name of the Nth scope for the analyzed entity.
      --  For 0 the result is always Standard,
      --  For 1 the result is Ada/Interfaces/System or user-defined,
      --  Etc.
      --
      --  Aspect Pure_Function is meant to improve performance when using
      --  this function as an array.

      ----------------
      -- Scope_Name --
      ----------------

      function Scope_Name (Nth : Scope_Index) return Name_Id is
        (Chars (Scopes (Scope_Id + Nth)));

      --  Start of processing for Is_Predefined_Potentially_Blocking

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
                 Entity
                   (Name (Get_Unit_Instantiation_Node (Parent_Scope)));
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

      case Scope_Name (2) is
         --  All subprograms in the child packages of these are blocking
         --
         --  Note: Ada.Directories.Hierarchical_File_Names seems nonblocking.
         --  We conciously ignore it, since it is not yet implemented in GNAT
         --  and extremely unlikely to be needed in nonblocking contexts.

         when Name_Directories
            | Name_Direct_IO
            | Name_Sequential_IO
            | Name_Streams
         =>
            return True;

         --  Detect Ada.Dispatching.Yield

         when Name_Dispatching
         =>
            return Scope_Name (3) = Name_Yield;

         --  Detect all subprograms in
         --    Ada.Strings.[[Wide_]Wide_]Unbounded.[[Wide_]Wide_]Text_IO.

         when Name_Strings
         =>
            return
              (case Scope_Name (3) is
                  when Name_Unbounded =>
                     Scope_Name (4) = Name_Text_IO,

                  when Name_Wide_Unbounded =>
                     Scope_Name (4) = Name_Wide_Text_IO,

                  when Name_Wide_Wide_Unbounded =>
                     Scope_Name (4) = Name_Wide_Wide_Text_IO,

                  when others =>
                     False);

         --  Detect Ada.Synchronous_Barriers.Wait_For_Release

         when Name_Synchronous_Barriers
         =>
            return Scope_Name (3) = Name_Wait_For_Release;

         --  Detect
         --    Ada.Synchronous_Task_Control.Suspend_Until_True
         --    Ada.Synchronous_Task_Control.EDF.
         --        Suspend_Until_True_And_Set_Deadline.

         when Name_Synchronous_Task_Control
         =>
            return
              Scope_Name (3) = Name_Suspend_Until_True
                 or else
              (Scope_Name (3) = Name_EDF
                 and then
               Scope_Name (4) = Name_Suspend_Until_True_And_Set_Deadline);

         --  Detect Ada.Task_Identification.Abort_Task

         when Name_Task_Identification
         =>
            return Scope_Name (3) = Name_Abort_Task;

         when Name_Text_IO
            | Name_Wide_Text_IO
            | Name_Wide_Wide_Text_IO
         =>
            case Scope_Name (3) is
               --  Operations on bounded/unbounded strings either print or read
               --  them and thus are potentially blocking.

               when Name_Bounded_IO
                  | Name_Unbounded_IO
               =>
                  return True;

               --  These generics have both blocking and nonblocking Put/Get

               when Name_Complex_IO
                  | Text_IO_Package_Name
               =>
                  --  The name of the subprogram (i.e. Put or Get) makes
                  --  no difference (and it troublesome to know because of
                  --  overriding). Blocking/Nonblocking status is determined
                  --  by the name of the first formal parameter.
                  --  * "File" means input/output to a specific file
                  --  * "Item" means input/output to a default file
                  --  * anything else means input/output to a string buffer
                  return Chars (First_Formal (E)) in Name_File | Name_Item;

               --  These packages operate only on internal data structers and
               --  thus are nonblocking.

               when Name_C_Streams
                  | Name_Text_Streams
                  | Name_Reset_Standard_Files
               =>
                  return False;

               --  Ada.Text_IO.Editing is nonblocking, except for Decimal_IO,
               --  where the only blocking subprograms are:
               --    procedure Put (File : Ada.Text_IO.File_Type; ...)
               --    procedure Put (Item : Num; ...)
               --  and they are also detected by the name of the first formal
               --  parameter.

               when Name_Editing
               =>
                  return
                    Scope_Name (4) = Name_Decimal_IO
                    and then Ekind (E) = E_Procedure
                    and then Chars (First_Formal (E)) in Name_File | Name_Item;

               --  Assume that all subprograms directly within Ada.Text_IO
               --  are potentially blocking. This is true for most of them,
               --  e.g. for Create/Open/Close/Delete, but in GNAT there few
               --  exceptions, e.g. Mode/Name/Form/Is_Open. However, they can
               --  be blocking in other compilers, so assume the worst case.

               when others
               =>
                  return True;
            end case;

         --  All other predefined subprograms are nonblocking

         when others =>
            return False;
      end case;

   end Is_Predefined_Potentially_Blocking;

   -----------------------------
   -- In_Private_Declarations --
   -----------------------------

   function In_Private_Declarations (Decl : Node_Id) return Boolean is
      Par : constant Node_Id := Parent (Decl);
   begin
      return
        Present (Par)
        and then Nkind (Par) = N_Package_Specification
        and then Is_List_Member (Decl)
        and then List_Containing (Decl) = Private_Declarations (Par);
   end In_Private_Declarations;

   -----------------------------
   -- In_Visible_Declarations --
   -----------------------------

   function In_Visible_Declarations (Decl : Node_Id) return Boolean is
      Par : constant Node_Id := Parent (Decl);
   begin
      return
        Present (Par)
        and then Nkind (Par) = N_Package_Specification
        and then Is_List_Member (Decl)
        and then List_Containing (Decl) = Visible_Declarations (Par);
   end In_Visible_Declarations;

   --------------------------
   -- In_Body_Declarations --
   --------------------------

   function In_Body_Declarations (Decl : Node_Id) return Boolean is
      Par : constant Node_Id := Parent (Decl);
   begin
      return
        Present (Par)
        and then Nkind (Par) = N_Package_Body
        and then Is_List_Member (Decl)
        and then List_Containing (Decl) = Declarations (Par);
   end In_Body_Declarations;

   -------------------------------------
   -- Is_Borrowing_Traversal_Function --
   -------------------------------------

   function Is_Borrowing_Traversal_Function (E : Entity_Id) return Boolean is
      (Is_Traversal_Function (E) and then not Is_Access_Constant (Etype (E)));

   ----------------------------------------
   -- Is_Invisible_Dispatching_Operation --
   ----------------------------------------

   function Is_Invisible_Dispatching_Operation
     (E : Entity_Id) return Boolean
   is
      Param : Entity_Id;
      Etyp  : Entity_Id;

   begin
      if Has_Controlling_Result (E) then
         Etyp := Etype (E);

      else
         Param := First_Entity (E);
         while Present (Param)
           and then Is_Formal (Param)
           and then not Is_Controlling_Formal (Param)
         loop
            Next_Entity (Param);
         end loop;

         Etyp := Etype (Param);
      end if;

      return Is_Private_Type (Etyp)
        and then not Is_Tagged_Type (Etyp)
        and then Present (Subprogram_Spec (E))
        and then In_Visible_Declarations (Subprogram_Spec (E));
   end Is_Invisible_Dispatching_Operation;

   ----------------------------------------
   -- Is_Local_Subprogram_Always_Inlined --
   ----------------------------------------

   function Is_Local_Subprogram_Always_Inlined
     (E : Entity_Id) return Boolean
   is
      function Has_Renaming_As_Body (E : Entity_Id) return Boolean;
      --  Returns true iff subprogram E is completed by renaming-as-body

      --------------------------
      -- Has_Renaming_As_Body --
      --------------------------

      function Has_Renaming_As_Body (E : Entity_Id) return Boolean is
         B : constant Node_Id := Subprogram_Body (E);
      begin
         return Present (B)
           and then Is_List_Member (B)
           and then Present (Prev (B))
           and then Nkind (Prev (B)) = N_Subprogram_Renaming_Declaration
           and then Corresponding_Spec (Prev (B)) = E;
      end Has_Renaming_As_Body;

   --  Start of processing for Is_Local_Subprogram_Always_Inlined

   begin
      --  Frontend inlining in GNATprove mode is disabled by switch -gnatdm

      if Debug.Debug_Flag_M then
         return False;

      --  A subprogram always inlined should have Body_To_Inline set and flag
      --  Is_Inlined_Always set to True. We check in addition that the address
      --  of the subprogram is not taken, as calls through callbacks cannot
      --  be analyzed in context. However, subprograms with renaming-as-body
      --  satisfy these conditions and are not always inlined.

      --  Also, subprograms of protected objects are never inlined

      else
         if Is_Subprogram (E)
           and then Is_Inlined_Always (E)
           and then not Address_Taken (E)
         then
            declare
               Spec : constant Node_Id := Subprogram_Spec (E);
            begin
               return Present (Spec)
                 and then Present (Body_To_Inline (Spec))
                 and then not Has_Renaming_As_Body (E);
            end;
         else
            return False;
         end if;
      end if;
   end Is_Local_Subprogram_Always_Inlined;

   -------------------------------------
   -- Is_Requested_Subprogram_Or_Task --
   -------------------------------------

   function Is_Requested_Subprogram_Or_Task (E : Entity_Id) return Boolean is
      Limit_Str : constant String :=
        GP_Subp_Marker & To_String (Gnat2Why_Args.Limit_Subp);
   begin
      return
        Ekind (E) in Subprogram_Kind | Task_Kind | E_Task_Body | Entry_Kind
          and then
        (Limit_Str = SPARK_Util.Subprograms.Subp_Location (E)
          or else
         Limit_Str = SPARK_Util.Subprograms.Subp_Body_Location (E));
   end Is_Requested_Subprogram_Or_Task;

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
           and then not Has_Contracts (E, Pragma_Precondition)
           and then not Has_Contracts (E, Pragma_Postcondition)
           and then No (Get_Pragma (E, Pragma_Contract_Cases))

           --  which corresponds to a shift or rotate
           and then
             (ECI (Name, Get_Name_String (Name_Shift_Right))
                or else
              ECI (Name, Get_Name_String (Name_Shift_Right_Arithmetic))
                or else
              ECI (Name, Get_Name_String (Name_Shift_Left))
                or else
              ECI (Name, Get_Name_String (Name_Rotate_Left))
                or else
              ECI (Name, Get_Name_String (Name_Rotate_Right)));
      end;
   end Is_Simple_Shift_Or_Rotate;

   ---------------------------
   -- Is_Traversal_Function --
   ---------------------------

   function Is_Traversal_Function (E : Entity_Id) return Boolean is
   begin
      return Ekind (E) = E_Function

        --  A function is said to be a traversal function if the result type of
        --  the function is an anonymous access-to-object type,

        and then Is_Anonymous_Access_Object_Type (Etype (E))

        --  the function has at least one formal parameter,

        and then Present (First_Formal (E))

        --  and the function's first parameter is of an access-to-object type.

        and then Is_Access_Type (Retysp (Etype (First_Formal (E))))
        and then
          Ekind (Directly_Designated_Type (Retysp (Etype (First_Formal (E)))))
            /= E_Subprogram_Type;
   end Is_Traversal_Function;

   ----------------------------------------
   -- Is_Unchecked_Deallocation_Instance --
   ----------------------------------------

   function Is_Unchecked_Deallocation_Instance
     (E : Entity_Id)
      return Boolean
   is
   begin
      --  The following condition is based on how Exp_Unc_Deallocation is
      --  called in the frontend expansion (this expansion is disabled in
      --  GNATprove mode).

      return
        Is_Intrinsic (E)
        and then Present (Parent (E))
        and then Present (Generic_Parent (Parent (E)))
        and then Chars (Generic_Parent (Parent (E)))
                         = Name_Unchecked_Deallocation;
   end Is_Unchecked_Deallocation_Instance;

   -----------------------------
   -- Is_Valid_Recursive_Call --
   -----------------------------

   procedure Is_Valid_Recursive_Call
     (Call          : Node_Id;
      Analyzed_Unit : Entity_Id;
      Result        : out Boolean;
      Explanation   : out Unbounded_String)
   is
      Called_Entity  : constant Entity_Id := Get_Called_Entity (Call);
      Recursive_Subp : constant Node_Id :=
        (if Is_Subprogram_Or_Entry (Analyzed_Unit)
         then Analyzed_Unit
         elsif Ekind (Analyzed_Unit) = E_Package
         then Directly_Enclosing_Subprogram_Or_Entry (Analyzed_Unit)
         else Empty);
      --  We only support recursive calls directly in a subprogram or
      --  in a package if the package itself is declared directly inside a
      --  subprogram.

      Mutually       : constant String :=
        (if Called_Entity = Recursive_Subp then "" else "mutually ");
      Prag           : Node_Id;

   begin
      --  We do not support recursive calls inside preconditions, as initial
      --  values of variants are evaluated after the precondition. Search
      --  for the first enclosing precondition.

      Prag := Parent (Call);
      while Present (Prag) loop
         exit when Nkind (Prag) = N_Pragma;
         Prag := Parent (Prag);
      end loop;

      if Present (Prag)
        and then Get_Pragma_Id (Pragma_Name (Prag)) in
          Pragma_Precondition | Pragma_Pre | Pragma_Pre_Class
      then
         Result := False;
         Explanation := To_Unbounded_String
           (Mutually & "recursive call should not appear in a "
            & "precondition");
      elsif Present (Prag)
        and then Get_Pragma_Id (Pragma_Name (Prag)) in
          Pragma_Subprogram_Variant
      then
         Result := False;
         Explanation := To_Unbounded_String
           (Mutually & "recursive call should not appear in a "
            & "subprogram variant");
      elsif No (Recursive_Subp) then
         Result := False;
         Explanation := To_Unbounded_String
           (Mutually & "recursive call should be located directly"
            & " inside a subprogram");
      elsif not Compatible_Variants (Called_Entity, Recursive_Subp) then
         Result := False;
         Explanation := To_Unbounded_String
           ("mutually recursive subprograms should have"
            & " compatible variants");
      else
         Explanation := To_Unbounded_String ("");
         Result := True;
      end if;
   end Is_Valid_Recursive_Call;

   ------------------------------------
   -- Is_Volatile_For_Internal_Calls --
   ------------------------------------

   function Is_Volatile_For_Internal_Calls (E : Entity_Id) return Boolean is
   begin
      return Ekind (E) = E_Function
        and then Is_Protected_Type (Scope (E))
        and then Is_Enabled_Pragma (Get_Pragma (E, Pragma_Volatile_Function));
   end Is_Volatile_For_Internal_Calls;

   -------------------
   -- Might_Be_Main --
   -------------------

   function Might_Be_Main (E : Entity_Id) return Boolean is
      Spec : Node_Id;
   begin
      --  This function mirrors tests in
      --    Lib.Write.Write_ALI.Output_Main_Program_Line
      --  which are more restrictive than those in
      --    Sem_Ch13.Analyze_Pragma.Check_In_Main_Program.

      --  Check if it is a library-level subprogram
      if not Is_Compilation_Unit (E) then
         return False;
      end if;

      Spec := Subprogram_Specification (E);

      pragma Assert (Nkind (Spec) in N_Function_Specification |
                                     N_Procedure_Specification);

      --  Check if it has no parameters
      if Present (Parameter_Specifications (Spec)) then
         return False;
      end if;

      --  Check if it is a procedure or a function that returns an integer
      return (case Nkind (Spec) is
                 when N_Procedure_Specification =>
                    True,

                 when N_Function_Specification =>
                    Is_Integer_Type (Etype (E)),

                 when others =>
                    raise Program_Error
             );
   end Might_Be_Main;

   ---------------------------------
   -- Process_Referenced_Entities --
   ---------------------------------

   procedure Process_Referenced_Entities (E : Entity_Id) is

      procedure Process_All
        (S    : Flow_Types.Flow_Id_Sets.Set;
         Kind : Formal_Kind);
      --  Process entities represented in S (as Flow_Ids)

      -----------------
      -- Process_All --
      -----------------

      procedure Process_All
        (S    : Flow_Types.Flow_Id_Sets.Set;
         Kind : Formal_Kind)
      is
      begin
         for F of S loop
            case F.Kind is
               when Direct_Mapping =>
                  Process (Get_Direct_Mapping_Id (F), Kind);

               when Magic_String =>
                  pragma Assert (Is_Opaque_For_Proof (F));

               when others =>
                  raise Program_Error;
            end case;
         end loop;
      end Process_All;

   begin
      --  Process global variables read or written in E

      case Ekind (E) is
         when E_Entry
            | E_Function
            | E_Procedure
            | E_Task_Type
            | E_Subprogram_Type
         =>
            declare
               Out_Ids    : Flow_Types.Flow_Id_Sets.Set;
               In_Ids     : Flow_Types.Flow_Id_Sets.Set;
               In_Out_Ids : Flow_Types.Flow_Id_Sets.Set;

            begin
               --  Also get references to global constants with variable inputs
               --  even if they are constants in Why.

               Flow_Utility.Get_Proof_Globals (Subprogram      => E,
                                               Reads           => In_Ids,
                                               Writes          => Out_Ids,
                                               Erase_Constants => False);

               In_Out_Ids := Flow_Types.Flow_Id_Sets.Intersection
                 (Out_Ids, In_Ids);
               In_Ids.Difference (In_Out_Ids);
               Out_Ids.Difference (In_Out_Ids);

               Process_All (In_Ids, E_In_Parameter);
               Process_All (In_Out_Ids, E_In_Out_Parameter);
               Process_All (Out_Ids, E_Out_Parameter);
            end;

         when E_Package =>
            if not Is_Wrapper_Package (E) then

               --  For packages, we use the Initializes aspect to get the
               --  variables referenced during elaboration.
               --  We don't do it for wrapper packages as Initializes are not
               --  generated for them.

               declare
                  Scop : constant Flow_Scope :=
                    Get_Flow_Scope (Package_Spec (E));
                  --  The scope of where the package is declared, not of the
                  --  package itself (because from the package itself we would
                  --  still see the constants that capture expressions of the
                  --  generic IN parameters).

                  Init_Map : constant Dependency_Maps.Map :=
                    Parse_Initializes (E, Scop);

               begin
                  for RHS of Init_Map loop
                     for Input of RHS loop

                        --  Expand Abstract_State if any

                        declare
                           Reads : constant Flow_Id_Sets.Set :=
                             Expand_Abstract_State (Input);
                        begin

                           --  Process the entity associated with the Flow_Ids

                           Process_All (Reads, E_In_Parameter);
                        end;
                     end loop;
                  end loop;
               end;
            end if;

         when others =>
            raise Program_Error;
      end case;
   end Process_Referenced_Entities;

   ------------------------
   -- Subp_Body_Location --
   ------------------------

   function Subp_Body_Location (E : Entity_Id) return String is
      Body_N : Node_Id;
      Body_E : Entity_Id := Empty;
      Slc    : Source_Ptr;
      Line   : Positive;

   begin
      case Ekind (E) is
         when E_Function
            | E_Procedure
            | E_Task_Type
            | Entry_Kind
         =>
            --  A derived task type has no body itself, so exclude this case
            if not Is_Derived_Type (E) then
               Body_E := Get_Body_Entity (E);
            end if;

         when E_Package =>
            Body_N := Package_Body (E);
            if Present (Body_N) then
               Body_E := Defining_Entity (Body_N);
            end if;

         when others =>
            null;
      end case;

      if Present (Body_E) then
         Slc := Sloc (Body_E);
         Line := Positive (Get_Physical_Line_Number (Slc));
         return
           GP_Subp_Marker & SPARK_Util.File_Name (Slc) & ":" & Image (Line, 1);
      else
         return "";
      end if;
   end Subp_Body_Location;

   -------------------
   -- Subp_Location --
   -------------------

   --  Only consider the first location in the chain of locations for an
   --  instantiation or an inlining. This matches the location given by
   --  users inside a generic/inlined subprogram.

   function Subp_Location (E : Entity_Id) return String is
      S : constant Subp_Type := Entity_To_Subp_Assumption (E);
      B : constant Base_Sloc := Subp_Sloc (S).First_Element;
   begin
      return GP_Subp_Marker & Base_Sloc_File (B) & ":" & Image (B.Line, 1);
   end Subp_Location;

   ---------------------------------
   -- Subp_Needs_Invariant_Checks --
   ---------------------------------

   function Subp_Needs_Invariant_Checks (E : Entity_Id) return Boolean is
      Read_Ids    : Flow_Types.Flow_Id_Sets.Set;
      Write_Ids   : Flow_Types.Flow_Id_Sets.Set;

      Is_External : constant Boolean := Is_Globally_Visible (E);
      --  The subprogram is an external or a boundary subprogram if it is
      --  visible from outside the current compilation unit.

   begin
      --  If the subprogram is boundary or external, we should check the type
      --  invariants of its parameters.

      if Is_External then
         declare
            Formal : Entity_Id := First_Formal (E);
         begin
            while Present (Formal) loop
               if Ekind (Formal) /= E_Out_Parameter
                 and then Invariant_Check_Needed (Etype (Formal))
               then
                  return True;
               end if;

               Next_Formal (Formal);
            end loop;
         end;
      end if;

      Flow_Utility.Get_Proof_Globals (Subprogram      => E,
                                      Reads           => Read_Ids,
                                      Writes          => Write_Ids,
                                      Erase_Constants => True);

      --  Consider invariants of the variables read by E

      for F of Read_Ids loop
         pragma Assert (F.Kind in Direct_Mapping | Magic_String);

         --  Magic_String are global state with no attached entities. As
         --  such state is translated as private in Why3, we do not need
         --  to consider any type invariant for it.

         if F.Kind = Direct_Mapping then
            declare
               E : constant Entity_Id := Get_Direct_Mapping_Id (F);

            begin
               --  Global variables accessed by the subprogram are either
               --  objects or concurrent types.

               if Invariant_Check_Needed (if Is_Type (E)
                                          then E
                                          else Etype (E))
               then
                  return True;
               end if;
            end;
         end if;
      end loop;

      return False;
   end Subp_Needs_Invariant_Checks;

   -------------------------------------
   -- Subprogram_Is_Ignored_For_Proof --
   -------------------------------------

   --  Functions generated by the frontend for aspects Type_Invariant and
   --  Default_Initial_Condition should be ignored. This does not include
   --  the functions generated for Predicate aspects, as these functions are
   --  translated to check absence of RTE in the predicate in the most general
   --  context.

   function Subprogram_Is_Ignored_For_Proof (E : Entity_Id) return Boolean is
     (Ekind (E) = E_Procedure and then
        (Is_Invariant_Procedure (E)
           or else
         Is_DIC_Procedure (E)));

   -----------------------------------
   -- Suspends_On_Suspension_Object --
   -----------------------------------

   function Suspends_On_Suspension_Object (E : Entity_Id) return Boolean is
      Scop : Entity_Id := E;
      --  Currently analyzed entity

      procedure Scope_Up;
      --  Climb up the scope

      --------------
      -- Scope_Up --
      --------------

      procedure Scope_Up is
      begin
         Scop := Scope (Scop);
      end Scope_Up;

   --  Start of processing for Suspends_On_Suspension_Object

   begin
      if Chars (Scop) = Name_Suspend_Until_True then
         Scope_Up;
      elsif Chars (Scop) = Name_Suspend_Until_True_And_Set_Deadline then
         Scope_Up;
         if Chars (Scop) = Name_EDF then
            Scope_Up;
         else
            return False;
         end if;
      else
         return False;
      end if;

      if Chars (Scop) = Name_Synchronous_Task_Control then
         Scope_Up;
      else
         return False;
      end if;

      if Chars (Scop) = Name_Ada then
         Scope_Up;
      else
         return False;
      end if;

      return Scop = Standard_Standard;
   end Suspends_On_Suspension_Object;

   --------------
   -- Get_Body --
   --------------

   function Get_Body (E : Entity_Id) return Node_Id is
   begin
      return (case Ekind (E) is
                 when Entry_Kind        => Entry_Body (E),
                 when E_Function
                    | E_Procedure       => Subprogram_Body (E),
                 when E_Protected_Type  => Protected_Body (E),
                 when E_Task_Type       => Task_Body (E),
                 when E_Subprogram_Type => Empty,
                 when others            => raise Program_Error);
   end Get_Body;

   ---------------------
   -- Get_Body_Entity --
   ---------------------

   function Get_Body_Entity (E : Entity_Id) return Entity_Id is
   begin
      return (case Ekind (E) is
                 when E_Entry         => Entry_Body_Entity (E),
                 when E_Task_Type     => Task_Body_Entity (E),
                 when Subprogram_Kind => Subprogram_Body_Entity (E),
                 when others          => raise Program_Error);
   end Get_Body_Entity;

end SPARK_Util.Subprograms;
