with Data_Structure;
with SPARK.Big_Intervals;  use SPARK.Big_Intervals;
with SPARK.Cut_Operations; use SPARK.Cut_Operations;

with Data_Structure.Internal_Models; use Data_Structure.Internal_Models;
with Data_Structure.Operations;      use Data_Structure.Operations;

package body Data_Structure
  with SPARK_Mode
is
   use Data_Structure.Operations.Advanced_Model;
   use Internal_Models.Index_To_Value_Maps;
   use Internal_Models.Memory_Index_Sequences;

   package Private_Model
     with Ghost
   is

      --  Proves E1 and E2 are equivalent, given both are equivalent to E
      function Prove_Equivalent_Elements
        (E1, E2, E : Element_Type) return Boolean
      with
        Pre  => Equivalent_Elements (E1, E) and Equivalent_Elements (E2, E),
        Post =>
          Prove_Equivalent_Elements'Result and Equivalent_Elements (E1, E2);

   end Private_Model;
   use Private_Model;

   package body Formal_Model is
      pragma Annotate (GNATprove, Unhide_Info, "Package_Body");

      --  Proves all elements equivalent to Item have the same Find position
      --  as Item.
      procedure Lemma_Find_Equivalent_Classes
        (Model             : M.Set;
         Allocated_Indexes : Internal_Models.Memory_Index_Sequences.Sequence;
         Values            : Internal_Models.Index_To_Value_Maps.Map;
         Item              : Element_Type)
      with
        Pre  => (for all I of Allocated_Indexes => Has_Key (Values, I)),
        Post =>
          (for all E of Model =>
             (if Equivalent_Elements (E, Item)
              then
                Internal_Models.Find (Allocated_Indexes, Values, E)
                = Internal_Models.Find (Allocated_Indexes, Values, Item)));

      --  Proves E.Find on Elements gives the same result as
      --  Internal_Models.Find on Allocated_Indexes.
      function Lemma_Find_Is_Find
        (Elements          : E.Sequence;
         Allocated_Indexes : Internal_Models.Memory_Index_Sequences.Sequence;
         Values            : Internal_Models.Index_To_Value_Maps.Map;
         Item              : Element_Type) return Boolean
      with
        Ghost,
        Pre  =>
          (for all I of Allocated_Indexes => Has_Key (Values, I))
          and then No_Duplicated_Elements (Allocated_Indexes, Values)
          and then E.Length (Elements) = Last (Allocated_Indexes)
          and then
            (for all P in 1 .. E.Last (Elements) =>
               E.Get (Elements, P)
               = Get (Values, Get (Allocated_Indexes, E.Big (P)))),
        Post =>
          Lemma_Find_Is_Find'Result
          and
            E.Big (Find (Elements, Item))
            = Internal_Models.Find (Allocated_Indexes, Values, Item);

      -------------------------
      -- E_Elements_Included --
      -------------------------

      function E_Elements_Included
        (Left : E.Sequence; Right : E.Sequence) return Boolean is
      begin
         for I in 1 .. E.Last (Left) loop
            declare
               J : constant Count_Type := Find (Right, E.Get (Left, I));
            begin
               if J = 0
                 or else
                   not Element_Logic_Equal (E.Get (Left, I), E.Get (Right, J))
               then
                  return False;
               end if;
            end;
            pragma
              Loop_Invariant
                (for all K in 1 .. I =>
                   Find (Right, E.Get (Left, K)) > 0
                   and then
                     Element_Logic_Equal
                       (E.Get (Right, Find (Right, E.Get (Left, K))),
                        E.Get (Left, K)));
         end loop;

         return True;
      end E_Elements_Included;

      -------------------------
      -- E_Elements_Included --
      -------------------------

      function E_Elements_Included
        (Left : E.Sequence; Model : M.Set; Right : E.Sequence) return Boolean
      is
      begin
         for I in 1 .. E.Last (Left) loop
            declare
               Item : constant Element_Type := E.Get (Left, I);
            begin
               if M.Contains (Model, Item) then
                  declare
                     J : constant Count_Type := Find (Right, E.Get (Left, I));
                  begin
                     if J = 0
                       or else not Element_Logic_Equal (Item, E.Get (Right, J))
                     then
                        return False;
                     end if;
                  end;
               end if;
            end;
            pragma
              Loop_Invariant
                (for all K in 1 .. I =>
                   (if M.Contains (Model, E.Get (Left, K))
                    then
                      Find (Right, E.Get (Left, K)) > 0
                      and then
                        Element_Logic_Equal
                          (E.Get (Right, Find (Right, E.Get (Left, K))),
                           E.Get (Left, K))));
         end loop;

         return True;
      end E_Elements_Included;

      -------------------------
      -- E_Elements_Included --
      -------------------------

      function E_Elements_Included
        (Container : E.Sequence;
         Model     : M.Set;
         Left      : E.Sequence;
         Right     : E.Sequence) return Boolean is
      begin
         for I in 1 .. E.Last (Container) loop
            declare
               Item : constant Element_Type := E.Get (Container, I);
            begin
               if M.Contains (Model, Item) then
                  declare
                     J : constant Count_Type :=
                       Find (Left, E.Get (Container, I));
                  begin
                     if J = 0
                       or else not Element_Logic_Equal (Item, E.Get (Left, J))
                     then
                        return False;
                     end if;
                  end;
               else
                  declare
                     J : constant Count_Type :=
                       Find (Right, E.Get (Container, I));
                  begin
                     if J = 0
                       or else not Element_Logic_Equal (Item, E.Get (Right, J))
                     then
                        return False;
                     end if;
                  end;
               end if;
            end;
            pragma
              Loop_Invariant
                (for all K in 1 .. I =>
                   (if M.Contains (Model, E.Get (Container, K))
                    then
                      Find (Left, E.Get (Container, K)) > 0
                      and then
                        Element_Logic_Equal
                          (E.Get (Left, Find (Left, E.Get (Container, K))),
                           E.Get (Container, K))
                    else
                      Find (Right, E.Get (Container, K)) > 0
                      and then
                        Element_Logic_Equal
                          (E.Get (Right, Find (Right, E.Get (Container, K))),
                           E.Get (Container, K))));
         end loop;

         return True;
      end E_Elements_Included;

      --------------
      -- Elements --
      --------------

      function Elements (Container : Set) return E.Sequence
      with
        Refined_Post =>
          E.Length (Elements'Result)
          = Last (HL_Model (Container).Allocated_Indexes)
          and then
            (for all P in 1 .. E.Last (Elements'Result) =>
               E.Get (Elements'Result, P)
               = Get
                   (HL_Model (Container).Values,
                    Get (HL_Model (Container).Allocated_Indexes, E.Big (P))))
          and then
            (for all Pos of HL_Model (Container).Values =>
               (if Internal_Models.Find
                     (HL_Model (Container).Allocated_Indexes, Pos)
                  > 0
                then
                  Get (HL_Model (Container).Values, Pos)
                  = E.Get
                      (Elements'Result,
                       E.Of_Big
                         (Internal_Models.Find
                            (HL_Model (Container).Allocated_Indexes, Pos)))))

          --  The last part can be proved from the above but requires manual
          --  instances of lemmas. So we repeat here so the postcondition
          --  can be verified.

          and then
            (for all Item of Model (Container) =>
               Internal_Models.Find
                 (HL_Model (Container).Allocated_Indexes,
                  HL_Model (Container).Values,
                  Item)
               = E.Big (Find (Elements'Result, Item)))
      is
         Position : Count_Type := Operations.First (Container);
         R        : E.Sequence;

      begin
         Lemma_HL_No_Duplicated_Indexes (Container);
         pragma
           Assert
             (Last (HL_Model (Container).Allocated_Indexes)
              = E.Big (Operations.Length (Container)));
         while Position /= 0 loop
            R :=
              E.Add
                (Container => R,
                 New_Item  => Operations.Element (Container, Position));

            pragma Loop_Invariant (Position /= 0);
            pragma Loop_Invariant (E.Length (R) > 0);
            pragma
              Loop_Invariant
                (E.Length (R)
                 = Internal_Models.Find
                     (HL_Model (Container).Allocated_Indexes, Position));
            pragma
              Loop_Invariant
                (for all P in 1 .. E.Last (R) =>
                   E.Get (R, P)
                   = Get
                       (HL_Model (Container).Values,
                        Get
                          (HL_Model (Container).Allocated_Indexes,
                           E.Big (P))));
            pragma
              Loop_Invariant
                (for all Pos of HL_Model (Container).Values =>
                   (if Internal_Models.Find
                         (HL_Model (Container).Allocated_Indexes, Pos)
                      > 0
                      and
                        Internal_Models.Find
                          (HL_Model (Container).Allocated_Indexes, Pos)
                        <= E.Length (R)
                    then
                      Get (HL_Model (Container).Values, Pos)
                      = E.Get
                          (R,
                           E.Of_Big
                             (Internal_Models.Find
                                (HL_Model (Container).Allocated_Indexes,
                                 Pos)))));
            pragma Loop_Variant (Increases => E.Last (R));

            Position := Operations.Next (Container, Position);
         end loop;

         pragma
           Assert
             (for all Item of Model (Container) =>
                Lemma_Find_Is_Find
                  (R,
                   HL_Model (Container).Allocated_Indexes,
                   HL_Model (Container).Values,
                   Item));

         return R;
      end Elements;

      ----------
      -- Find --
      ----------

      function Find
        (Container : E.Sequence; Item : Element_Type) return Count_Type
      with
        Refined_Post =>
          (if Find'Result > 0
           then
             Find'Result <= E.Last (Container)
             and Equivalent_Elements (Item, E.Get (Container, Find'Result))
           else
             (for all I in 1 .. E.Last (Container) =>
                not Equivalent_Elements (Item, E.Get (Container, I))))
      is
      begin
         for I in 1 .. E.Last (Container) loop
            if Equivalent_Elements (Item, E.Get (Container, I)) then
               return I;
            end if;
            pragma
              Loop_Invariant
                (for all K in 1 .. I =>
                   not Equivalent_Elements (Item, E.Get (Container, K)));
         end loop;
         return 0;
      end Find;

      -----------------------------------
      -- Lemma_Find_Equivalent_Classes --
      -----------------------------------

      procedure Lemma_Find_Equivalent_Classes
        (Model             : M.Set;
         Allocated_Indexes : Internal_Models.Memory_Index_Sequences.Sequence;
         Values            : Internal_Models.Index_To_Value_Maps.Map;
         Item              : Element_Type) is
      begin
         pragma
           Assert
             (for all E of Model =>
                (if Equivalent_Elements (E, Item)
                 then
                   By
                     (Internal_Models.Find (Allocated_Indexes, Values, E)
                      = Internal_Models.Find (Allocated_Indexes, Values, Item),
                      (if Internal_Models.Find
                            (Allocated_Indexes, Values, Item)
                         > 0
                       then
                         Prove_Equivalent_Elements
                           (Get
                              (Values,
                               Get
                                 (Allocated_Indexes,
                                  Internal_Models.Find
                                    (Allocated_Indexes, Values, Item))),
                            E,
                            Item))
                      and
                        (if Internal_Models.Find (Allocated_Indexes, Values, E)
                           > 0
                         then
                           Prove_Equivalent_Elements
                             (Get
                                (Values,
                                 Get
                                   (Allocated_Indexes,
                                    Internal_Models.Find
                                      (Allocated_Indexes, Values, E))),
                              Item,
                              E)))));
      end Lemma_Find_Equivalent_Classes;

      ------------------------
      -- Lemma_Find_Is_Find --
      ------------------------

      function Lemma_Find_Is_Find
        (Elements          : E.Sequence;
         Allocated_Indexes : Internal_Models.Memory_Index_Sequences.Sequence;
         Values            : Internal_Models.Index_To_Value_Maps.Map;
         Item              : Element_Type) return Boolean is
      begin
         pragma
           Assert
             (if Internal_Models.Find (Allocated_Indexes, Values, Item) > 0
                and Find (Elements, Item) > 0
              then
                Prove_Equivalent_Elements
                  (E.Get (Elements, Find (Elements, Item)),
                   E.Get
                     (Elements,
                      E.Of_Big
                        (Internal_Models.Find
                           (Allocated_Indexes, Values, Item))),
                   Item));

         return True;
      end Lemma_Find_Is_Find;

      ----------------------------
      -- Lift_Abstraction_Level --
      ----------------------------

      procedure Lift_Abstraction_Level (Container : Set) is null;

      function Mapping_Preserved
        (E_Left  : E.Sequence;
         E_Right : E.Sequence;
         P_Left  : P.Map;
         P_Right : P.Map) return Boolean
      is ((for all C of P_Left =>
             P.Has_Key (P_Right, C)
             and then P.Get (P_Left, C) <= E.Last (E_Left)
             and then P.Get (P_Right, C) <= E.Last (E_Right)
             and then
               Element_Logic_Equal
                 (E.Get (E_Left, P.Get (P_Left, C)),
                  E.Get (E_Right, P.Get (P_Right, C))))
          and then E_Elements_Included (E_Left, E_Right));

      function Mapping_Preserved_Except
        (E_Left   : E.Sequence;
         E_Right  : E.Sequence;
         P_Left   : P.Map;
         P_Right  : P.Map;
         Position : Cursor) return Boolean
      is (for all C of P_Left =>
            P.Has_Key (P_Right, C)
            and then
              (if C /= Position
               then
                 P.Get (P_Left, C) <= E.Last (E_Left)
                 and then P.Get (P_Right, C) <= E.Last (E_Right)
                 and then
                   Element_Logic_Equal
                     (E.Get (E_Left, P.Get (P_Left, C)),
                      E.Get (E_Right, P.Get (P_Right, C)))));

      -----------
      -- Model --
      -----------

      function Model (Container : Set) return M.Set
      with
        Refined_Post =>
          (for all I of HL_Model (Container).Allocated_Indexes =>
             M.Contains (Model'Result, Get (HL_Model (Container).Values, I)))
          and then
            (for all E of Model'Result =>
               Internal_Models.Find
                 (HL_Model (Container).Allocated_Indexes,
                  HL_Model (Container).Values,
                  E)
               /= 0)
          and then
            M.Length (Model'Result)
            = Last (HL_Model (Container).Allocated_Indexes)
      is
         Position : Count_Type := Operations.First (Container);
         R        : M.Set;

      begin
         Lemma_HL_No_Duplicated_Indexes (Container);
         while Position /= 0 loop
            R :=
              M.Add
                (Container => R,
                 Item      => Operations.Element (Container, Position));

            Lemma_Find_Equivalent_Classes
              (R,
               HL_Model (Container).Allocated_Indexes,
               HL_Model (Container).Values,
               Operations.Element (Container, Position));
            pragma Loop_Invariant (M.Length (R) > 0);
            pragma Loop_Invariant (Position /= 0);
            pragma
              Loop_Invariant
                (M.Length (R)
                 = Internal_Models.Find
                     (HL_Model (Container).Allocated_Indexes, Position));
            pragma
              Loop_Invariant
                (for all K in Interval'(1, M.Length (R)) =>
                   M.Contains
                     (R,
                      Get
                        (HL_Model (Container).Values,
                         Get (HL_Model (Container).Allocated_Indexes, K))));
            pragma
              Loop_Invariant
                (for all E of R =>
                   Internal_Models.Find
                     (HL_Model (Container).Allocated_Indexes,
                      HL_Model (Container).Values,
                      E)
                   > 0);
            pragma
              Loop_Invariant
                (for all E of R =>
                   Internal_Models.Find
                     (HL_Model (Container).Allocated_Indexes,
                      HL_Model (Container).Values,
                      E)
                   <= M.Length (R));
            pragma
              Loop_Variant
                (Decreases =>
                   Last (HL_Model (Container).Allocated_Indexes)
                   - M.Length (R));

            Position := Operations.Next (Container, Position);
         end loop;

         return R;
      end Model;

      ---------------
      -- Positions --
      ---------------

      function Positions (Container : Set) return P.Map
      with
        Refined_Post =>
          (for all Cu of Positions'Result => Cu.Node > 0)
          and then
            (for all Pos in 1 .. Operations.Length (Container) =>
               P.Has_Key
                 (Positions'Result,
                  Cursor'
                    (Node =>
                       Get
                         (HL_Model (Container).Allocated_Indexes,
                          E.Big (Pos)))))
          and then
            (for all Pos in Positive_Count_Type =>
               (Internal_Models.Find
                  (HL_Model (Container).Allocated_Indexes, Pos)
                > 0)
               = P.Has_Key (Positions'Result, Cursor'(Node => Pos)))
          and then
            (for all Cu of Positions'Result =>
               E.Big (P.Get (Positions'Result, Cu))
               = Internal_Models.Find
                   (HL_Model (Container).Allocated_Indexes, Cu.Node))
      is
         Position : Count_Type := Operations.First (Container);
         R        : P.Map;

      begin
         Lemma_HL_No_Duplicated_Indexes (Container);
         for I in 1 .. Operations.Length (Container) loop
            R :=
              P.Add
                (Container => R, New_Key => (Node => Position), New_Item => I);

            pragma Loop_Invariant (Position > 0);
            pragma Loop_Invariant (P.Length (R) > 0);
            pragma
              Loop_Invariant
                (Position
                 = Get (HL_Model (Container).Allocated_Indexes, E.Big (I)));
            pragma Loop_Invariant (P.Length (R) = E.Big (I));
            pragma
              Loop_Invariant
                (for all Cu of R =>
                   Cu.Node > 0
                   and then
                     Internal_Models.Find
                       (HL_Model (Container).Allocated_Indexes, Cu.Node)
                     <= E.Big (I));
            pragma
              Loop_Invariant
                (for all Pos in 1 .. I =>
                   P.Has_Key
                     (R,
                      Cursor'
                        (Node =>
                           Get
                             (HL_Model (Container).Allocated_Indexes,
                              E.Big (Pos)))));
            pragma
              Loop_Invariant
                (for all Cu of R =>
                   E.Big (P.Get (R, Cu))
                   = Internal_Models.Find
                       (HL_Model (Container).Allocated_Indexes, Cu.Node));
            pragma
              Loop_Invariant
                (for all Pos in Positive_Count_Type =>
                   In_Range
                     (Internal_Models.Find
                        (HL_Model (Container).Allocated_Indexes, Pos),
                      1,
                      E.Big (I))
                   = P.Has_Key (R, Cursor'(Node => Pos)));

            Position := Operations.Next (Container, Position);
         end loop;

         return R;
      end Positions;

   end Formal_Model;

   package body Private_Model is

      -------------------------------
      -- Prove_Equivalent_Elements --
      -------------------------------

      function Prove_Equivalent_Elements
        (E1, E2, E : Element_Type) return Boolean is
      begin
         Lemma_Equivalent_Elements_Transitive (E1, E, E2);
         return True;
      end Prove_Equivalent_Elements;
   end Private_Model;

   function Contains (Container : Set; Item : Element_Type) return Boolean
   is (Operations.Contains (Container, Item));

   ------------
   -- Delete --
   ------------

   procedure Delete (Container : in out Set; Position : in out Cursor) is
   begin
      Operations.Delete (Container, Position.Node);
      Position := No_Element;
   end Delete;

   ------------
   -- Delete --
   ------------

   procedure Delete (Container : in out Set; Item : Element_Type) is
      Old_Item  : constant Element_Type :=
        Operations.Element (Container, Find (Container, Item).Node)
      with Ghost;
      Model_Old : constant M.Set := Model (Container)
      with Ghost;
   begin
      Operations.Delete_Key (Container, Item);
      pragma
        Assert
          (for all E of Model_Old =>
             (if not Contains (Model (Container), E)
              then
                By
                  (Equivalent_Elements (E, Item),
                   Prove_Equivalent_Elements (E, Item, Old_Item))));
   end Delete;

   function Element (Container : Set; Position : Cursor) return Element_Type
   is (Operations.Element (Container, Position.Node));

   ---------------
   -- Empty_Set --
   ---------------

   function Empty_Set (Capacity : Count_Type := 10) return Set is
   begin
      return Operations.Empty_Set (Capacity);
   end Empty_Set;

   -------------
   -- Exclude --
   -------------

   procedure Exclude (Container : in out Set; Item : Element_Type) is
      Old_Item  : constant Element_Type :=
        (if not Contains (Container, Item)
         then Item
         else Operations.Element (Container, Find (Container, Item).Node))
      with Ghost;
      Model_Old : constant M.Set := Model (Container)
      with Ghost;
   begin
      Operations.Delete_Key (Container, Item);
      pragma
        Assert
          (for all E of Model_Old =>
             (if not Contains (Model (Container), E)
              then
                By
                  (Equivalent_Elements (E, Item),
                   Prove_Equivalent_Elements (E, Item, Old_Item))));
   end Exclude;

   function Find (Container : Set; Item : Element_Type) return Cursor
   is (Node => Operations.Find (Container, Item));

   function Find_Bucket
     (X : Element_Type; Modulus : Hash_Type) return Hash_Type
   is (Hash (X) mod Modulus + 1);

   function Has_Element (Container : Set; Position : Cursor) return Boolean
   is (Position.Node /= 0
       and then Operations.Has_Element (Container, Position.Node));

   -------------
   -- Include --
   -------------

   procedure Include (Container : in out Set; New_Item : Element_Type) is
      Inserted : Boolean;
      Position : Count_Type;

   begin
      Operations.Conditional_Insert (Container, New_Item, Position, Inserted);
      if not Inserted then
         Operations.Replace (Container, Position, New_Item);
         pragma Assert (Position = Find (Container, New_Item).Node);
      end if;
   end Include;

   ------------
   -- Insert --
   ------------

   procedure Insert
     (Container : in out Set;
      New_Item  : Element_Type;
      Position  : out Cursor;
      Inserted  : out Boolean) is
   begin
      Operations.Conditional_Insert
        (Container, New_Item, Position.Node, Inserted);
   end Insert;

   ------------
   -- Insert --
   ------------

   procedure Insert (Container : in out Set; New_Item : Element_Type) is
      Inserted        : Boolean;
      Unused_Position : Count_Type;

   begin
      Operations.Conditional_Insert
        (Container, New_Item, Unused_Position, Inserted);
      pragma Assert (Inserted);
   end Insert;

   ---------------
   -- Invariant --
   ---------------

   function Invariant (S : Set) return Boolean
   with
     Refined_Post =>
       Invariant'Result = Operations.Advanced_Model.HL_Invariant (S)
       and then (if Default_Init (S) then Invariant'Result)
   is
   begin
      Operations.Advanced_Model.Prove_Invariant_On_Default (S);
      return Operations.Advanced_Model.HL_Invariant (S);
   end Invariant;

   --------------
   -- Is_Empty --
   --------------

   function Is_Empty (Container : Set) return Boolean
   with
     Refined_Post =>
       Is_Empty'Result = (Operations.Length (Container) = 0)
       and then (if Default_Init (Container) then Is_Empty'Result)
   is
   begin
      return Operations.Is_Empty (Container);
   end Is_Empty;

   -------------------------------------------
   -- Lemma_Equivalent_Elements_Find_Bucket --
   -------------------------------------------

   procedure Lemma_Equivalent_Elements_Find_Bucket
     (X, Y : Element_Type; Modulus : Hash_Type) is
   begin
      Lemma_Equivalent_Elements_Hash (X, Y);
      pragma
        Assert
          (if Equivalent_Elements (X, Y)
           then Hash (X) mod Modulus + 1 = Hash (Y) mod Modulus + 1);
   end Lemma_Equivalent_Elements_Find_Bucket;

   function Length (Container : Set) return Count_Type
   is (Operations.Length (Container));

   -------------
   -- Replace --
   -------------

   procedure Replace (Container : in out Set; New_Item : Element_Type) is
      Position : constant Positive_Count_Type :=
        Operations.Find (Container, New_Item);

   begin
      Operations.Replace (Container, Position, New_Item);
      pragma Assert (Position = Find (Container, New_Item).Node);
   end Replace;

   ---------------------
   -- Replace_Element --
   ---------------------

   procedure Replace_Element
     (Container : in out Set; Position : Cursor; New_Item : Element_Type)
   is

      procedure Lemma_Is_Move_Find
        (S1 : Sequence; P1, P2 : Big_Positive; S2 : Sequence)
      with
        Ghost,
        Pre  => Is_Move (S1, P1, P2, S2),
        Post =>
          (for all E in Positive_Count_Type =>
             (Internal_Models.Find (S1, E) > 0)
             = (Internal_Models.Find (S2, E) > 0));

      procedure Lemma_Is_Move_Find
        (S1 : Sequence; P1, P2 : Big_Positive; S2 : Sequence)
      is null;

      Allocated_Indexes_Old : constant Sequence :=
        HL_Model (Container).Allocated_Indexes
      with Ghost;
   begin
      Operations.Replace_Element (Container, Position.Node, New_Item);
      Lemma_Is_Move_Find
        (Allocated_Indexes_Old,
         Internal_Models.Find (Allocated_Indexes_Old, Position.Node),
         Internal_Models.Find
           (HL_Model (Container).Allocated_Indexes, Position.Node),
         HL_Model (Container).Allocated_Indexes);
   end Replace_Element;

end Data_Structure;
