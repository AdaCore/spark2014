------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--           F L O W . A N A L Y S I S . A N T I A L I A S I N G            --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                  Copyright (C) 2013-2017, Altran UK Limited              --
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

with Flow_Classwide;      use Flow_Classwide;
with Flow_Error_Messages; use Flow_Error_Messages;
with Flow_Utility;        use Flow_Utility;
with Nlists;              use Nlists;
with Output;              use Output;
with Sem_Aux;             use Sem_Aux;
with Sem_Eval;            use Sem_Eval;
with Sem_Util;            use Sem_Util;
with Sprint;              use Sprint;
with VC_Kinds;            use VC_Kinds;
with Why;

package body Flow.Analysis.Antialiasing is

   Trace_Antialiasing : constant Boolean := False;
   --  Enable this for gratuitous tracing output for aliasing
   --  detection.

   subtype Computed_Aliasing_Result is Aliasing_Check_Result
     range Impossible .. Definite_Aliasing;

   subtype Non_Obvious_Aliasing_Check_Result is Aliasing_Check_Result
     range No_Aliasing .. Definite_Aliasing;

   package Aliasing_Statuses is new Ada.Containers.Hashed_Maps
     (Key_Type        => Node_Id,
      Element_Type    => Aliasing_Check_Result,
      Hash            => Node_Hash,
      Equivalent_Keys => "=");

   Aliasing_Status : Aliasing_Statuses.Map := Aliasing_Statuses.Empty_Map;

   function Check_Range (AL, AH : Node_Id;
                         BL, BH : Node_Id)
                         return Non_Obvious_Aliasing_Check_Result;
   --  Checks two ranges for potential overlap.

   function Aliasing (A,        B        : Node_Id;
                      Formal_A, Formal_B : Node_Id)
                      return Computed_Aliasing_Result
   with Pre => Present (Formal_A);
   --  Returns if A and B alias.

   function Cannot_Alias (F : Node_Id) return Boolean
   with Pre => Present (F) and then
               Nkind (F) in N_Entity and then
               Is_Formal (F);
   --  Check if the given formal parameter cannot possibly alias with
   --  others: it is a scalar in parameter.

   procedure Check_Node_Against_Node
     (FA       : in out Flow_Analysis_Graphs;
      A, B     : Node_Or_Entity_Id;
      A_Formal : Entity_Id;
      B_Formal : Entity_Id;
      Status   : out Computed_Aliasing_Result)
   with Pre => Present (A_Formal);
   --  Checks the two nodes for aliasing and issues an error message
   --  if appropriate. The formal for B can be Empty, in which case we
   --  assume it is a global.

   procedure Check_Parameter_Against_Parameters_And_Globals
     (FA     : in out Flow_Analysis_Graphs;
      Status : out Computed_Aliasing_Result;
      Actual : Node_Id);
   --  Checks the given actual against all other parameters and
   --  globals.

   procedure Update_Status (Status         : in out Computed_Aliasing_Result;
                            Current_Status : Computed_Aliasing_Result);
   --  Updates the aliasing Status only if the Current_Status is worse (in
   --  terms of the ordering given but the type Computed_Aliasing_Result).

   -----------------
   -- Check_Range --
   -----------------

   function Check_Range (AL, AH : Node_Id;
                         BL, BH : Node_Id)
                         return Non_Obvious_Aliasing_Check_Result
   is
      function LT (A, B : Node_Id) return Boolean;
      --  Return true iff A < B.

      function GE (A, B : Node_Id) return Boolean;
      --  Return true iff A >= B.

      function Empty (A, B : Node_Id) return Boolean;
      --  Return true iff A > B.

      function Full (A, B : Node_Id) return Boolean;
      --  Return true iff A <= B.

      function LT (A, B : Node_Id) return Boolean is
      begin
         return Compile_Time_Compare (A, B, True) = LT;
      end LT;

      function GE (A, B : Node_Id) return Boolean is
      begin
         return Compile_Time_Compare (A, B, True) in GE | GT | EQ;
      end GE;

      function Empty (A, B : Node_Id) return Boolean is
      begin
         return Compile_Time_Compare (A, B, True) = GT;
      end Empty;

      function Full (A, B : Node_Id) return Boolean is
      begin
         return Compile_Time_Compare (A, B, True) in LT | LE | EQ;
      end Full;
   begin
      if Empty (AL, AH)
        or else Empty (BL, BH)
        or else LT (AH, BL)
        or else LT (BH, AL)
      then
         --  We definitely have a different, non-overlapping ranges;
         --  or at least one of them is empty.
         return No_Aliasing;

      elsif Full (AL, AH) and then Full (BL, BH) and then
        ((GE (AH, BL) and then GE (BH, AL))
           or else
         (GE (BH, AL) and then GE (AH, BL)))
      then
         --  We definitely have overlapping, non-empty ranges.
         return Definite_Aliasing;

      else
         --  We don't know.
         return Possible_Aliasing;
      end if;
   end Check_Range;

   --------------
   -- Aliasing --
   --------------

   function Aliasing (A,        B        : Node_Id;
                      Formal_A, Formal_B : Node_Id)
                      return Computed_Aliasing_Result
   is
      --  Expressions are not interesting. Names are, but only some:
      Is_Interesting : constant array (Node_Kind) of Boolean :=
        (
         --  Direct name
         N_Identifier                => True,
         N_Expanded_Name             => True,
         N_Defining_Identifier       => True,

         --  Explicit dereference is not in SPARK

         --  Indexed component and slices
         N_Indexed_Component         => True,
         N_Slice                     => True,

         --  Selected components
         N_Selected_Component        => True,

         --  Attribute references (the only interesting one is 'access
         --  which is not in SPARK)

         --  Type conversion
         N_Qualified_Expression      => True,
         N_Type_Conversion           => True,

         --  Function call is boring in SPARK as it can't return
         --  access, except for unchecked conversions.
         N_Unchecked_Type_Conversion => True,

         --  Character literals, qualified expressions are boring

         --  Generalized reference and indexing are suitably expanded

         --  Everything else must be an expression and is thus not
         --  interesting
         others                      => False);

      Is_Root : constant array (Node_Kind) of Boolean :=
        (N_Identifier          => True,
         N_Expanded_Name       => True,
         N_Defining_Identifier => True,
         others                => False);

      Is_Conversion : constant array (Node_Kind) of Boolean :=
        (N_Qualified_Expression      => True,
         N_Type_Conversion           => True,
         N_Unchecked_Type_Conversion => True,
         others                      => False);

      function Down_One_Level (N : Node_Id) return Node_Id
        with Pre => Is_Interesting (Nkind (N)) and then
                    not Is_Root (Nkind (N));
      --  Goes down the parse tree by one level. For example:
      --     * R.X.Y       ->  R.X
      --     * R.X         ->  R
      --     * A (12)      ->  A
      --     * Wibble (X)  ->  X

      function Find_Root (N : Node_Id) return Node_Id
        with Pre  => Is_Interesting (Nkind (N)),
             Post => Is_Root (Nkind (Find_Root'Result))
                     or else not Is_Interesting (Nkind (Find_Root'Result));
      --  Calls Down_One_Level until we find an identifier. For example:
      --    * R.X.Y       ->  R
      --    * A (12)      ->  A
      --    * Wibble (X)  ->  X

      function Get_Root_Entity (N : Node_Id) return Entity_Id
      is (case Nkind (N) is
             when N_Defining_Identifier => N,
             when others => Entity (N))
      with Pre => Is_Root (Nkind (N));
      --  Returns the entity attached to the identifier N. Deals with
      --  the case where we have an N_Defining_Identifier (which is
      --  its own entity).

      function Same_Entity (A, B : Node_Id) return Boolean
        is (Get_Root_Entity (A) = Get_Root_Entity (B))
      with Pre => Is_Root (Nkind (A)) and Is_Root (Nkind (B));
      --  Checks if A and B refer to the same entity.

      function Up_Ignoring_Conversions (N   : Node_Id;
                                        Top : Node_Id)
                                       return Node_Id
      with Pre  => Is_Interesting (Nkind (N)),
           Post => Is_Interesting (Nkind (Up_Ignoring_Conversions'Result));
      --  Goes up the parse tree (calling Parent), but no higher than
      --  Top. If we find an type conversion of some kind we keep
      --  going.

      --------------------
      -- Down_One_Level --
      --------------------

      function Down_One_Level (N : Node_Id) return Node_Id is
      begin
         case Nkind (N) is
            when N_Indexed_Component
               | N_Slice
               | N_Selected_Component
            =>
               return Prefix (N);

            when N_Type_Conversion
               | N_Unchecked_Type_Conversion
               | N_Qualified_Expression
            =>
               return Expression (N);

            when others =>
               raise Program_Error;
         end case;
      end Down_One_Level;

      ---------------
      -- Find_Root --
      ---------------

      function Find_Root (N : Node_Id) return Node_Id
      is
         R : Node_Id := N;
      begin
         while Is_Interesting (Nkind (R)) and then not Is_Root (Nkind (R)) loop
            R := Down_One_Level (R);
         end loop;
         return R;
      end Find_Root;

      -----------------------------
      -- Up_Ignoring_Conversions --
      -----------------------------

      function Up_Ignoring_Conversions (N   : Node_Id;
                                        Top : Node_Id)
                                        return Node_Id
      is
         P : Node_Id := Parent (N);
      begin
         while P /= Top and then Is_Conversion (Nkind (P)) loop
            P := Parent (P);
         end loop;
         return P;
      end Up_Ignoring_Conversions;

      Ptr_A, Ptr_B      : Node_Id;
      Definitive_Result : Boolean := True;

   --  Start of processing for Aliasing

   begin

      --  First we check if either of the nodes is interesting as
      --  non-interesting nodes cannot introduce aliasing.

      if Trace_Antialiasing then
         Write_Str ("antialiasing: checking ");
         Sprint_Node (A);
         Write_Str (" <--> ");
         Sprint_Node (B);
         Write_Eol;
      end if;

      if not Is_Interesting (Nkind (A)) then
         if Trace_Antialiasing then
            Write_Line ("   -> A is not interesting");
         end if;
         return Impossible;
      elsif not Is_Interesting (Nkind (B)) then
         if Trace_Antialiasing then
            Write_Line ("   -> B is not interesting");
         end if;
         return Impossible;
      end if;

      if Cannot_Alias (Formal_A) then
         if Trace_Antialiasing then
            Write_Line ("   -> A does not require aa checking");
         end if;
         return Impossible;
      elsif Present (Formal_B) and then Cannot_Alias (Formal_B) then
         if Trace_Antialiasing then
            Write_Line ("   -> B does not require aa checking");
         end if;
         return Impossible;
      end if;

      --  Ok, so both nodes might potentially alias. We now need to
      --  work out the root nodes of each expression.

      Ptr_A := Find_Root (A);
      Ptr_B := Find_Root (B);

      if Trace_Antialiasing then
         Write_Str ("   -> root of A: ");
         Sprint_Node (Ptr_A);
         Write_Eol;
         Write_Str ("   -> root of B: ");
         Sprint_Node (Ptr_B);
         Write_Eol;
      end if;

      if not Is_Root (Nkind (Ptr_A)) then
         if Trace_Antialiasing then
            Write_Line ("   -> root of A is not interesting");
         end if;
         return Impossible;
      elsif not Is_Root (Nkind (Ptr_B)) then
         if Trace_Antialiasing then
            Write_Line ("   -> root of B is not interesting");
         end if;
         return Impossible;
      end if;

      --  A quick sanity check. If the root nodes refer to different
      --  entities then we cannot have aliasing.

      if not Same_Entity (Ptr_A, Ptr_B) then
         if Trace_Antialiasing then
            Write_Line ("   -> different root entities");
         end if;
         return Impossible;
      end if;

      --  Ok, we now know that the root nodes refer to the same
      --  entity, we now need to walk up the tree and see if we differ
      --  somehow. For example, right now we might have:
      --     * A,              A           --  illegal
      --     * A.X.Y (1 .. J), A.X         --  illegal
      --     * A.X,            A.Y         --  OK
      --     * A (J),          A (K)       --  maybe illegal
      --     * A.X,            Wibble (A)  --  illegal
      --     * A,              Wibble (A)  --  illegal
      --  etc.
      --
      --  Also, we know that Is_Root holds for Ptr_A and Ptr_B, which
      --  means that we are dealing with an identifier and not an
      --  unchecked conversion, etc.

      if Trace_Antialiasing then
         Write_Line ("   -> same root entity");
      end if;

      while Ptr_A /= A and then Ptr_B /= B loop
         --  Go up the tree one level. If we hit an unchecked
         --  conversion or type conversion we 'ignore' it. For
         --  example:
         --     * R.X  ->  R.X.Y
         --     * R    ->  Wibble (R).X
         --     * R    ->  Wibble (R)    (if Wibble (R) is the top)

         Ptr_A := Up_Ignoring_Conversions (Ptr_A, A);
         Ptr_B := Up_Ignoring_Conversions (Ptr_B, B);

         pragma Assert (not Is_Root (Nkind (Ptr_A)));
         pragma Assert (not Is_Root (Nkind (Ptr_B)));

         --  Check if we are dealing with an type conversion *now*. If
         --  so, we have aliasing.

         if Is_Conversion (Nkind (Ptr_A)) or else
           Is_Conversion (Nkind (Ptr_B))
         then
            if Trace_Antialiasing then
               Write_Line ("   -> identical tree followed by conversion");
            end if;
            return Definite_Aliasing;
         end if;

         --  We have now gone up one level on each side. We need to
         --  check the two fields.

         if Nkind (Ptr_A) = Nkind (Ptr_B) then
            --  We definitely need to check this. Some possibilities:
            --     R.X         <-->  R.X.Y
            --     R.X         <-->  R.Z
            --     A (5)       <-->  A (J).Wibble
            --     A (1 .. 3)  <-->  A (K .. L)
            if Trace_Antialiasing then
               Write_Str ("   -> checking same structure at ");
               Sprint_Node (Ptr_A);
               Write_Str (" <--> ");
               Sprint_Node (Ptr_B);
               Write_Eol;
            end if;

            case Nkind (Ptr_A) is
               when N_Selected_Component =>
                  if not Same_Entity (Selector_Name (Ptr_A),
                                      Selector_Name (Ptr_B))
                  then
                     if Trace_Antialiasing then
                        Write_Line ("   -> selectors differ");
                     end if;
                     return No_Aliasing;
                  end if;

               when N_Indexed_Component =>
                  declare
                     Index_A : Node_Id := First (Expressions (Ptr_A));
                     Index_B : Node_Id := First (Expressions (Ptr_B));
                  begin
                     while Present (Index_A) loop
                        pragma Assert (Present (Index_B));

                        case Compile_Time_Compare (Index_A, Index_B, True) is
                           when LT | GT | NE =>
                              if Trace_Antialiasing then
                                 Write_Str ("   -> index ");
                                 Sprint_Node (Index_A);
                                 Write_Str (" and ");
                                 Sprint_Node (Index_B);
                                 Write_Line (" statically differ");
                              end if;
                              return No_Aliasing;

                           when EQ =>
                              null;

                           when others =>
                              Definitive_Result := False;
                        end case;

                        Index_A := Next (Index_A);
                        Index_B := Next (Index_B);
                     end loop;
                  end;

               when N_Slice =>
                  case Check_Range (Low_Bound (Discrete_Range (Ptr_A)),
                                    High_Bound (Discrete_Range (Ptr_A)),
                                    Low_Bound (Discrete_Range (Ptr_B)),
                                    High_Bound (Discrete_Range (Ptr_B))) is
                     when No_Aliasing =>
                        if Trace_Antialiasing then
                           Write_Str ("   -> slice ");
                           Sprint_Node (Discrete_Range (Ptr_A));
                           Write_Str (" and ");
                           Sprint_Node (Discrete_Range (Ptr_B));
                           Write_Line (" statically distinct");
                        end if;
                        return No_Aliasing;

                     when Definite_Aliasing =>
                        null;

                     when Possible_Aliasing =>
                        Definitive_Result := False;
                  end case;

               when others =>
                  raise Why.Unexpected_Node;
            end case;

         elsif (Nkind (Ptr_A) = N_Slice and then
                  Nkind (Ptr_B) = N_Indexed_Component) or else
           (Nkind (Ptr_A) = N_Indexed_Component and then
              Nkind (Ptr_B) = N_Slice)
         then
            --  We also need to check this. One possibility:
            --     A (1 .. 3)  <-->  A (J)

            --  If the user *really* wants this we can implement
            --  it. For now skip this as its potentially quite hard as
            --  we need to sync up with the other expression.
            --
            --  Consider this: A (4 .. 10) (5 .. 8) (3)

            if Trace_Antialiasing then
               Write_Line
                 ("   -> slice v.s. index is difficult - bailing out");
            end if;

            return Possible_Aliasing;

         else
            --  We have previously established that things might
            --  possibly alias, which means the tree should have been
            --  similar enough. Look for the bug in the above code.
            raise Why.Unexpected_Node;
         end if;

      end loop;

      --  The tree so far was exactly the same, so we A and B
      --  definitely alias.

      if Trace_Antialiasing then
         Write_Line ("   -> identical tree so far, hit end");
         if Definitive_Result then
            Write_Line ("   -> result is definitive");
         end if;
      end if;

      if Definitive_Result then
         return Definite_Aliasing;
      else
         return Possible_Aliasing;
      end if;
   end Aliasing;

   ------------------
   -- Cannot_Alias --
   ------------------

   function Cannot_Alias (F : Node_Id) return Boolean is
   begin
      case Ekind (F) is
         when E_In_Parameter =>
            --  According to SPARK and Ada RMs here we should test for by-copy
            --  type (e.g. using Is_By_Copy_Type). However, it seems better
            --  to treat private types as really private and check if by-copy
            --  property can be deduced from the public declaration only. If
            --  not then we are conservative and assume the worst case, i.e.
            --  that the type is by-reference. See O916-007.
            return Is_Elementary_Type (Etype (F));

         when E_In_Out_Parameter
            | E_Out_Parameter
         =>
            return False;

         when others =>
            raise Program_Error;
      end case;
   end Cannot_Alias;

   -----------------------------
   -- Check_Node_Against_Node --
   -----------------------------

   procedure Check_Node_Against_Node
     (FA       : in out Flow_Analysis_Graphs;
      A, B     : Node_Or_Entity_Id;
      A_Formal : Entity_Id;
      B_Formal : Entity_Id;
      Status   : out Computed_Aliasing_Result)
   is
      Msg    : Unbounded_String := Null_Unbounded_String;
      B_Node : Node_Id;
   begin
      Status := Aliasing (A, B, A_Formal, B_Formal);

      case Status is
         when Impossible =>
            return;

         when Possible_Aliasing
            | Definite_Aliasing
         =>
            null;

         when No_Aliasing =>
            Append (Msg, "non-aliasing of ");
      end case;

      Append (Msg, "formal parameter");
      if Present (B_Formal) then
         Append (Msg, "s & and &");
         B_Node := B_Formal;
      else
         --  ??? maybe have a special message for generated globals
         Append (Msg, " & and global &");
         B_Node := B;
      end if;

      case Status is
         when Possible_Aliasing =>
            Append (Msg, " might be aliased");

         when Definite_Aliasing =>
            Append (Msg, " are aliased");

         when No_Aliasing =>
            Append (Msg, " proved");

         when Impossible =>
            raise Program_Error;
      end case;

      Error_Msg_Flow (FA       => FA,
                      Msg      => To_String (Msg),
                      Severity =>
                        (case Status is
                         when No_Aliasing       => Info_Kind,
                         when Possible_Aliasing => Medium_Check_Kind,
                         when Definite_Aliasing => High_Check_Kind,
                         when Impossible        => raise Program_Error),
                      N        => A,
                      F1       => Direct_Mapping_Id (A_Formal),
                      F2       => Direct_Mapping_Id (B_Node),
                      Tag      => Aliasing,
                      SRM_Ref  => (if Status = No_Aliasing
                                   then ""
                                   else "6.4.2"));
   end Check_Node_Against_Node;

   ----------------------------------------------------
   -- Check_Parameter_Against_Parameters_And_Globals --
   ----------------------------------------------------

   procedure Check_Parameter_Against_Parameters_And_Globals
     (FA     : in out Flow_Analysis_Graphs;
      Status : out Computed_Aliasing_Result;
      Actual : Node_Id)
   is
      Formal         : Entity_Id;
      Call           : Node_Id;
      Is_Out         : Boolean;
      Current_Status : Computed_Aliasing_Result;

   begin
      Status := Impossible;
      --  Set the status to the best Computed_Aliasing_Result. This would be
      --  later updated if a worse status would be computed.

      --  Work out who we are.

      Find_Actual (Actual, Formal, Call);
      Is_Out := Ekind (Formal) in E_Out_Parameter | E_In_Out_Parameter;

      --  The general idea here is to make sure none of the globals
      --  and parameters overlap. If we have a procedure with
      --  parameters X, Y and Z and globals A and B, then we check the
      --  following:
      --
      --     X v.s. (Y, Z, A, B)
      --     Y v.s. (   Z, A, B)
      --     Z v.s. (      A, B)
      --
      --  In particular we do not check the globals against each other and
      --  we do not check combinations of parameters which we have already
      --  seen. This is implemented by this procedure having the same loop as
      --  Check_Parameter_Against_Parameters_And_Globals and by only checking
      --  parameters once we have seen our parameter we compare against.

      --  Check against parameters.

      declare
         P            : Node_Id;
         Other        : Node_Id;
         Other_Formal : Entity_Id;
         Other_Call   : Node_Id;
         Other_Is_Out : Boolean;
         Found_Myself : Boolean := False;
      begin
         P := First (Parameter_Associations (Call));
         while Present (P) loop
            Other := (if Nkind (P) = N_Parameter_Association
                      then Explicit_Actual_Parameter (P)
                      else P);
            Find_Actual (Other, Other_Formal, Other_Call);
            Other_Is_Out := Ekind (Other_Formal) in E_Out_Parameter
                                                  | E_In_Out_Parameter;
            pragma Assert (Call = Other_Call);

            if Actual = Other then
               --  We don't check against ourselves, but we do not ???
               --  when we have found ourselves, see below...
               Found_Myself := True;

            elsif not Found_Myself then
               --  We don't need to check B against A because we
               --  already would have checked A against B.
               null;

            elsif Is_Out or Other_Is_Out then
               --  We only check for aliasing if at least one of the
               --  parameters is an out paramter.
               Check_Node_Against_Node
                 (FA       => FA,
                  A        => Actual,
                  B        => Other,
                  A_Formal => Formal,
                  B_Formal => Other_Formal,
                  Status   => Current_Status);
               Update_Status (Status, Current_Status);
            end if;

            Next (P);
         end loop;
      end;

      --  Check against globals.

      declare
         Globals : Global_Flow_Ids;

         Subprogram  : constant Entity_Id := Get_Called_Entity (Call);
      begin
         Get_Globals (Subprogram => Subprogram,
                      Scope      => FA.B_Scope,
                      Classwide  => Flow_Classwide.Is_Dispatching_Call (Call),
                      Globals    => Globals);
         if Is_Out then
            for R of Globals.Reads loop
               --  No use in checking both the read and the write of
               --  an in out global.
               if not Globals.Writes.Contains (Change_Variant (R, Out_View))
               then
                  case R.Kind is
                     when Direct_Mapping =>
                        Check_Node_Against_Node
                          (FA       => FA,
                           A        => Actual,
                           B        => Get_Direct_Mapping_Id (R),
                           A_Formal => Formal,
                           B_Formal => Empty,
                           Status   => Current_Status);
                        Update_Status (Status, Current_Status);

                     when Magic_String =>
                        --  If we don't have a name for the global, by
                        --  definition we can't possibly reference it in a
                        --  parameter.
                        null;

                     when others =>
                        raise Why.Unexpected_Node;
                  end case;
               end if;
            end loop;
         end if;
         for W of Globals.Writes loop
            case W.Kind is
               when Direct_Mapping =>
                  Check_Node_Against_Node
                    (FA       => FA,
                     A        => Actual,
                     B        => Get_Direct_Mapping_Id (W),
                     A_Formal => Formal,
                     B_Formal => Empty,
                     Status   => Current_Status);
                  Update_Status (Status, Current_Status);

               when Magic_String =>
                  --  If we don't have a name for the global, by
                  --  definition we can't possibly reference it in a
                  --  parameter.
                  null;

               when others =>
                  raise Why.Unexpected_Node;
            end case;
         end loop;
      end;
   end Check_Parameter_Against_Parameters_And_Globals;

   --------------------------
   -- Check_Procedure_Call --
   --------------------------

   procedure Check_Procedure_Call
     (FA : in out Flow_Analysis_Graphs;
      N  : Node_Id)
   is
   begin

      --  Check out and in out parameters against other parameters and globals

      declare
         P      : Node_Id;
         Actual : Node_Id;
         Formal : Entity_Id;
         Call   : Node_Id;

         Current_Status : Computed_Aliasing_Result;
         Status         : Computed_Aliasing_Result := Impossible;

      begin
         P := First (Parameter_Associations (N));
         while Present (P) loop
            Actual := (if Nkind (P) = N_Parameter_Association
                       then Explicit_Actual_Parameter (P)
                       else P);
            Find_Actual (Actual, Formal, Call);
            pragma Assert (Call = N);

            Check_Parameter_Against_Parameters_And_Globals (FA,
                                                            Current_Status,
                                                            Actual);
            Update_Status (Status, Current_Status);
            Next (P);
         end loop;
         --  Store in the map the aliasing status of the current procedure call
         Aliasing_Status.Insert (N, Status);
      end;

      --  ??? Need to check for aliasing between abstract state and computed
      --  globals.

   end Check_Procedure_Call;

   -----------------------------------
   -- Get_Aliasing_Status_For_Proof --
   -----------------------------------

   function Get_Aliasing_Status_For_Proof (N : Node_Id)
                                           return Aliasing_Check_Result
   is
     (if Aliasing_Status.Contains (N)
      then Aliasing_Status (N)
      else Unchecked);

   -------------------
   -- Update_Status --
   -------------------

   procedure Update_Status (Status         : in out Computed_Aliasing_Result;
                            Current_Status : Computed_Aliasing_Result)
   is
   begin
      if Current_Status > Status then
         Status := Current_Status;
      end if;
   end Update_Status;

end Flow.Analysis.Antialiasing;
