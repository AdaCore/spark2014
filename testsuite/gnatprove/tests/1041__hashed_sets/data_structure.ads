with SPARK.Containers.Functional.Sets;
with SPARK.Containers.Functional.Vectors;
with SPARK.Containers.Functional.Maps;

with SPARK.Big_Integers; use SPARK.Big_Integers;

package Data_Structure
  with SPARK_Mode
is
   type Hash_Type is mod 2 ** 32;
   type Count_Type is range 0 .. 2 ** 31 - 1;
   subtype Positive_Count_Type is Count_Type range 1 .. Count_Type'Last;
   subtype Positive_Hash_Type is Hash_Type range 1 .. Hash_Type'Last;

   type Element_Type is new Integer;

   --  Whether X and Y are considered equal for set membership purposes
   function Equivalent_Elements (X, Y : Element_Type) return Boolean
   with Global => null, Import;

   --  Lemmas stating the Equivalent_Elements is an equivalent relation. Do
   --  not use Automated_Instantiation for transitivity as it is hard to
   --  aply without an explicit pivot.

   --  Proves X is equivalent to itself
   procedure Lemma_Equivalent_Elements_Refexive (X : Element_Type)
   with
     Global   => null,
     Always_Terminates,
     Import,
     Ghost,
     Post     => Equivalent_Elements (X, X),
     Annotate => (GNATprove, Automatic_Instantiation);
   --  Proves equivalence is symmetric
   procedure Lemma_Equivalent_Elements_Symmetric (X, Y : Element_Type)
   with
     Global   => null,
     Always_Terminates,
     Import,
     Ghost,
     Post     => Equivalent_Elements (X, Y) = Equivalent_Elements (Y, X),
     Annotate => (GNATprove, Automatic_Instantiation);
   --  Proves equivalence is transitive
   procedure Lemma_Equivalent_Elements_Transitive (X, Y, Z : Element_Type)
   with
     Global => null,
     Always_Terminates,
     Import,
     Ghost,
     Post   =>
       (if Equivalent_Elements (X, Y) and Equivalent_Elements (Y, Z)
        then Equivalent_Elements (X, Z));

   --  Hash function for elements; equivalent elements must have equal hashes
   function Hash (X : Element_Type) return Hash_Type
   with Global => null, Import;

   --  Hash is compatible with the equivalence relation

   procedure Lemma_Equivalent_Elements_Hash (X, Y : Element_Type)
   with
     Global => null,
     Always_Terminates,
     Import,
     Ghost,
     Post   => (if Equivalent_Elements (X, Y) then Hash (X) = Hash (Y));

   type Set
     (Capacity : Count_Type;
      Modulus  : Positive_Hash_Type)
   is
     private
   with Default_Initial_Condition => Is_Empty (Set);

   --  Creates a new empty set with the given Capacity
   function Empty_Set (Capacity : Count_Type := 10) return Set
   with
     Post =>
       Is_Empty (Empty_Set'Result)
       and then Empty_Set'Result.Capacity = Capacity;

   type Cursor is record
      Node : Count_Type;
   end record;

   No_Element : constant Cursor := (Node => 0);

   --  Number of elements in the set
   function Length (Container : Set) return Count_Type
   with Global => null, Post => Length'Result <= Container.Capacity;

   pragma Unevaluated_Use_Of_Old (Allow);

   package Formal_Model
     with Ghost
   is

      ------------------
      -- Formal Model --
      ------------------

      subtype Positive_Count_Type is Count_Type range 1 .. Count_Type'Last;

      package M is new
        SPARK.Containers.Functional.Sets
          (Element_Type                   => Element_Type,
           Equivalent_Elements            => Equivalent_Elements,
           Equivalent_Elements_Reflexive  =>
             Lemma_Equivalent_Elements_Refexive,
           Equivalent_Elements_Symmetric  =>
             Lemma_Equivalent_Elements_Symmetric,
           Equivalent_Elements_Transitive =>
             Lemma_Equivalent_Elements_Transitive);

      function "=" (Left : M.Set; Right : M.Set) return Boolean renames M."=";

      function "<=" (Left : M.Set; Right : M.Set) return Boolean
      renames M."<=";

      package E is new
        SPARK.Containers.Functional.Vectors
          (Element_Type        => Element_Type,
           Index_Type          => Positive_Count_Type,
           "="                 => "=",
           Equivalent_Elements => "=");

      function Element_Logic_Equal (Left, Right : Element_Type) return Boolean
      renames E.Element_Logic_Equal;

      function "=" (Left : E.Sequence; Right : E.Sequence) return Boolean
      renames E."=";

      function "<" (Left : E.Sequence; Right : E.Sequence) return Boolean
      renames E."<";

      function "<=" (Left : E.Sequence; Right : E.Sequence) return Boolean
      renames E."<=";

      function Find
        (Container : E.Sequence; Item : Element_Type) return Count_Type
      with
        Global => null,
        Post   =>
          (if Find'Result > 0
           then
             Find'Result <= E.Last (Container)
             and Equivalent_Elements (Item, E.Get (Container, Find'Result)));
      --  Search for Item in Container

      function E_Elements_Included
        (Left : E.Sequence; Right : E.Sequence) return Boolean
      with
        Global => null,
        Post   =>
          E_Elements_Included'Result
          = (for all I in 1 .. E.Last (Left) =>
               Find (Right, E.Get (Left, I)) > 0
               and then
                 Element_Logic_Equal
                   (E.Get (Right, Find (Right, E.Get (Left, I))),
                    E.Get (Left, I)));
      pragma
        Annotate (GNATprove, Inline_For_Proof, Entity => E_Elements_Included);
      --  The elements of Left are contained in Right

      function E_Elements_Included
        (Left : E.Sequence; Model : M.Set; Right : E.Sequence) return Boolean
      with
        Global => null,
        Post   =>
          E_Elements_Included'Result
          = (for all I in 1 .. E.Last (Left) =>
               (if M.Contains (Model, E.Get (Left, I))
                then
                  Find (Right, E.Get (Left, I)) > 0
                  and then
                    Element_Logic_Equal
                      (E.Get (Right, Find (Right, E.Get (Left, I))),
                       E.Get (Left, I))));
      pragma
        Annotate (GNATprove, Inline_For_Proof, Entity => E_Elements_Included);
      --  The elements of Container contained in Model are in Right

      function E_Elements_Included
        (Container : E.Sequence;
         Model     : M.Set;
         Left      : E.Sequence;
         Right     : E.Sequence) return Boolean
      with
        Global => null,
        Post   =>
          E_Elements_Included'Result
          = (for all I in 1 .. E.Last (Container) =>
               (if M.Contains (Model, E.Get (Container, I))
                then
                  Find (Left, E.Get (Container, I)) > 0
                  and then
                    Element_Logic_Equal
                      (E.Get (Left, Find (Left, E.Get (Container, I))),
                       E.Get (Container, I))
                else
                  Find (Right, E.Get (Container, I)) > 0
                  and then
                    Element_Logic_Equal
                      (E.Get (Right, Find (Right, E.Get (Container, I))),
                       E.Get (Container, I))));
      pragma
        Annotate (GNATprove, Inline_For_Proof, Entity => E_Elements_Included);
      --  The elements of Container contained in Model are in Left and others
      --  are in Right.

      package P is new
        SPARK.Containers.Functional.Maps
          (Key_Type                       => Cursor,
           Element_Type                   => Positive_Count_Type,
           Equivalent_Keys                => "=",
           Enable_Handling_Of_Equivalence => False);

      function "=" (Left : P.Map; Right : P.Map) return Boolean renames P."=";

      function "<=" (Left : P.Map; Right : P.Map) return Boolean
      renames P."<=";

      function Mapping_Preserved
        (E_Left  : E.Sequence;
         E_Right : E.Sequence;
         P_Left  : P.Map;
         P_Right : P.Map) return Boolean
      with
        Global => null,
        Post   =>
          (if Mapping_Preserved'Result
           then
             P.Keys_Included (P_Left, P_Right)
             and E_Elements_Included (E_Left, E_Right)
             and
               (for all C of P_Left =>
                  Element_Logic_Equal
                    (E.Get (E_Left, P.Get (P_Left, C)),
                     E.Get (E_Right, P.Get (P_Right, C)))));
      --  Right contains all the cursors of Left
      --  Right contains all the elements of Left
      --  Mappings from cursors to elements induced by E_Left, P_Left
      --  and E_Right, P_Right are the same.

      function Mapping_Preserved_Except
        (E_Left   : E.Sequence;
         E_Right  : E.Sequence;
         P_Left   : P.Map;
         P_Right  : P.Map;
         Position : Cursor) return Boolean
      with
        Global => null,
        Post   =>
          (if Mapping_Preserved_Except'Result
           then
             P.Keys_Included (P_Left, P_Right)
             and
               (for all C of P_Left =>
                  (if C /= Position
                   then
                     Element_Logic_Equal
                       (E.Get (E_Left, P.Get (P_Left, C)),
                        E.Get (E_Right, P.Get (P_Right, C))))));
      --  Right contains all the cursors of Left
      --  Mappings from cursors to elements induced by E_Left, P_Left
      --  and E_Right, P_Right are the same except for Position.

      function Model (Container : Set) return M.Set
      with
        --  The high-level model of a set is a set of elements. Neither cursors
        --  nor order of elements are represented in this model. Elements are
        --  modeled up to equivalence.

        Global => null,
        Post   => M.Length (Model'Result) = E.Big (Length (Container));

      function Elements (Container : Set) return E.Sequence
      with
        --  The Elements sequence represents the underlying list structure of
        --  sets that is used for iteration. It stores the actual Elements of
        --  elements in the set. It does not model cursors.

        Global => null,
        Post   =>
          E.Last (Elements'Result) = Length (Container)

          --  It only contains keys contained in Model

          and
            (for all Item of Elements'Result =>
               M.Contains (Model (Container), Item))

          --  It contains all the elements contained in Model

          and
            (for all Item of Model (Container) =>
               Find (Elements'Result, Item) > 0)

          --  It has no duplicate

          and
            (for all I in 1 .. Length (Container) =>
               Find (Elements'Result, E.Get (Elements'Result, I)) = I)

          and
            (for all I in 1 .. Length (Container) =>
               (for all J in 1 .. Length (Container) =>
                  (if Equivalent_Elements
                        (E.Get (Elements'Result, I),
                         E.Get (Elements'Result, J))
                   then I = J)));

      function Positions (Container : Set) return P.Map
      with
        --  The Positions map is used to model cursors. It only contains valid
        --  cursors and maps them to their position in the container.

        Global => null,
        Post   =>
          not P.Has_Key (Positions'Result, No_Element)
          and then
            (for all I of Positions'Result =>
               P.Get (Positions'Result, I) in 1 .. Length (Container)
               and then
                 (for all J of Positions'Result =>
                    (if P.Get (Positions'Result, I)
                       = P.Get (Positions'Result, J)
                     then I = J)));
      --  Positions of cursors are smaller than the container's length
      --  No two cursors have the same position. Note that we do not
      --  state that there is a cursor in the map for each position,
      --  as it is rarely needed.

      procedure Lift_Abstraction_Level (Container : Set)
      with
        --  Lift_Abstraction_Level is a ghost procedure that does nothing but
        --  assume that we can access the same elements by iterating over
        --  positions or cursors.
        --  This information is not generally useful except when switching from
        --  a low-level, cursor-aware view of a container, to a high-level,
        --  position-based view.

        Ghost,
        Global => null,
        Post   =>
          (for all Item of Elements (Container) =>
             (for some I of Positions (Container) =>
                Element_Logic_Equal
                  (E.Get
                     (Elements (Container), P.Get (Positions (Container), I)),
                   Item)));

      function Contains (C : M.Set; K : Element_Type) return Boolean
      renames M.Contains;
      --  To improve readability of contracts, we rename the function used to
      --  search for an element in the model to Contains.

   end Formal_Model;
   use Formal_Model;

   --  Whether the set contains no elements
   function Is_Empty (Container : Set) return Boolean
   with
     Global => null,
     Post   =>
       Is_Empty'Result = M.Is_Empty (Model (Container))
       and Is_Empty'Result = (Length (Container) = 0);

   --  Whether Position is a valid cursor into the set
   function Has_Element (Container : Set; Position : Cursor) return Boolean
   with
     Global => null,
     Post   =>
       Has_Element'Result = P.Has_Key (Positions (Container), Position);

   --  The element designated by Position
   function Element (Container : Set; Position : Cursor) return Element_Type
   with
     Global => null,
     Pre    => Has_Element (Container, Position),
     Post   =>
       Element'Result
       = E.Get (Elements (Container), P.Get (Positions (Container), Position));

   --  Whether an element equivalent to Item is in the set
   function Contains (Container : Set; Item : Element_Type) return Boolean
   with
     Global => null,
     Post   => Contains'Result = Contains (Model (Container), Item);

   --  Returns a cursor to an element equivalent to Item, or No_Element if not
   --  found.
   function Find (Container : Set; Item : Element_Type) return Cursor
   with
     Global         => null,
     Contract_Cases =>

       --  If Item is not contained in Container, Find returns No_Element

       (not Contains (Model (Container), Item) => Find'Result = No_Element,

        --  Otherwise, Find returns a valid cursor in Container

        others                                 =>
          P.Has_Key (Positions (Container), Find'Result)
          and
            P.Get (Positions (Container), Find'Result)
            = Find (Elements (Container), Item)

          --  The element designated by the result of Find is Item

          and Equivalent_Elements (Element (Container, Find'Result), Item));

   --  Replaces the element at Position with New_Item
   procedure Replace_Element
     (Container : in out Set; Position : Cursor; New_Item : Element_Type)
   with
     Global => null,
     Pre    =>
       Has_Element (Container, Position)
       and then
         (Equivalent_Elements (Element (Container, Position), New_Item)
          or else not Contains (Container, New_Item)),
     Post   =>
       Length (Container)
       = Length (Container)'Old

         --  Position now maps to New_Item

       and Element_Logic_Equal (Element (Container, Position), New_Item)

       --  New_Item is contained in Container

       and Contains (Model (Container), New_Item)

       --  Other elements are preserved

       and
         M.Included_Except
           (Model (Container)'Old,
            Model (Container),
            Element (Container, Position)'Old)
       and
         M.Included_Except (Model (Container), Model (Container)'Old, New_Item)

       --  Mapping from cursors to elements is preserved

       and
         Mapping_Preserved_Except
           (E_Left   => Elements (Container)'Old,
            E_Right  => Elements (Container),
            P_Left   => Positions (Container)'Old,
            P_Right  => Positions (Container),
            Position => Position);

   --  Removes the element at Position; sets Position to No_Element
   procedure Delete (Container : in out Set; Position : in out Cursor)
   with
     Global => null,
     Pre    => Has_Element (Container, Position),
     Post   =>
       Position = No_Element
       and Length (Container) = Length (Container)'Old - 1

       --  The element at position Position is no longer in Container

       and not Contains (Container, Element (Container, Position)'Old)
       and not P.Has_Key (Positions (Container), Position'Old)

       --  Other elements are preserved

       and Model (Container) <= Model (Container)'Old
       and
         M.Included_Except
           (Model (Container)'Old,
            Model (Container),
            Element (Container, Position)'Old)

       --  Mapping from cursors to elements is preserved

       and
         Mapping_Preserved
           (E_Left  => Elements (Container),
            E_Right => Elements (Container)'Old,
            P_Left  => Positions (Container),
            P_Right => Positions (Container)'Old)
       and
         P.Keys_Included_Except
           (Positions (Container)'Old, Positions (Container), Position'Old);

   --  Removes the element equivalent to Item
   procedure Delete (Container : in out Set; Item : Element_Type)
   with
     Global => null,
     Pre    => Contains (Container, Item),
     Post   =>
       Length (Container) = Length (Container)'Old - 1

       --  Item is no longer in Container

       and not Contains (Container, Item)

       --  Other elements are preserved

       and Model (Container) <= Model (Container)'Old
       and M.Included_Except (Model (Container)'Old, Model (Container), Item)

       --  Mapping from cursors to elements is preserved

       and
         Mapping_Preserved
           (E_Left  => Elements (Container),
            E_Right => Elements (Container)'Old,
            P_Left  => Positions (Container),
            P_Right => Positions (Container)'Old)
       and
         P.Keys_Included_Except
           (Positions (Container)'Old,
            Positions (Container),
            Find (Container, Item)'Old);

   --  Removes an element equivalent to Item if present; no-op otherwise
   procedure Exclude (Container : in out Set; Item : Element_Type)
   with
     Global         => null,
     Post           => not Contains (Container, Item),
     Contract_Cases =>

       --  If Item is not in Container, nothing is changed

       (not Contains (Container, Item) =>
          Model (Container) = Model (Container)'Old
          and E.Equal (Elements (Container), Elements (Container)'Old)
          and Positions (Container) = Positions (Container)'Old,

        --  Otherwise, Item is removed from Container

        others                         =>
          Length (Container) = Length (Container)'Old - 1

          --  Other elements are preserved

          and Model (Container) <= Model (Container)'Old
          and
            M.Included_Except (Model (Container)'Old, Model (Container), Item)

          --  Mapping from cursors to elements is preserved

          and
            Mapping_Preserved
              (E_Left  => Elements (Container),
               E_Right => Elements (Container)'Old,
               P_Left  => Positions (Container),
               P_Right => Positions (Container)'Old)
          and
            P.Keys_Included_Except
              (Positions (Container)'Old,
               Positions (Container),
               Find (Container, Item)'Old));

   --  Inserts New_Item; returns its cursor and whether it was newly inserted
   procedure Insert
     (Container : in out Set;
      New_Item  : Element_Type;
      Position  : out Cursor;
      Inserted  : out Boolean)
   with
     Global         => null,
     Pre            =>
       Length (Container) < Container.Capacity
       or Contains (Container, New_Item),
     Post           =>
       Contains (Container, New_Item)
       and Has_Element (Container, Position)
       and Equivalent_Elements (Element (Container, Position), New_Item),
     Contract_Cases =>

       --  If New_Item is already in Container, it is not modified and
       --  Inserted is set to False.

       (Contains (Container, New_Item) =>
          not Inserted
          and Model (Container) = Model (Container)'Old
          and E.Equal (Elements (Container), Elements (Container)'Old)
          and Positions (Container) = Positions (Container)'Old,

        --  Otherwise, New_Item is inserted in Container and Inserted is set
        --  to True.

        others                         =>
          Inserted
          and Length (Container) = Length (Container)'Old + 1

          --  Position now maps to New_Item

          and
            Element_Logic_Equal
              (Element (Container, Position), E.Copy_Element (New_Item))

          --  Other elements are preserved

          and Model (Container)'Old <= Model (Container)
          and
            M.Included_Except
              (Model (Container), Model (Container)'Old, New_Item)

          --  Mapping from cursors to elements is preserved

          and
            Mapping_Preserved
              (E_Left  => Elements (Container)'Old,
               E_Right => Elements (Container),
               P_Left  => Positions (Container)'Old,
               P_Right => Positions (Container))
          and
            P.Keys_Included_Except
              (Positions (Container), Positions (Container)'Old, Position));

   --  Inserts New_Item; requires it to not already be present
   procedure Insert (Container : in out Set; New_Item : Element_Type)
   with
     Global => null,
     Pre    =>
       Length (Container) < Container.Capacity
       and then not Contains (Container, New_Item),
     Post   =>
       Length (Container) = Length (Container)'Old + 1
       and Contains (Container, New_Item)
       and
         Element_Logic_Equal
           (Element (Container, Find (Container, New_Item)),
            E.Copy_Element (New_Item))

       --  Other elements are preserved

       and Model (Container)'Old <= Model (Container)
       and
         M.Included_Except (Model (Container), Model (Container)'Old, New_Item)

       --  Mapping from cursors to elements is preserved

       and
         Mapping_Preserved
           (E_Left  => Elements (Container)'Old,
            E_Right => Elements (Container),
            P_Left  => Positions (Container)'Old,
            P_Right => Positions (Container))
       and
         P.Keys_Included_Except
           (Positions (Container),
            Positions (Container)'Old,
            Find (Container, New_Item));

   --  Inserts New_Item, replacing any equivalent element already present
   procedure Include (Container : in out Set; New_Item : Element_Type)
   with
     Global         => null,
     Pre            =>
       Length (Container) < Container.Capacity
       or Contains (Container, New_Item),
     Post           =>
       Contains (Container, New_Item)
       and
         Element_Logic_Equal
           (Element (Container, Find (Container, New_Item)),
            E.Copy_Element (New_Item)),
     Contract_Cases =>

       --  If an element equivalent to New_Item is already in Container, it
       --  is replaced by New_Item.

       (Contains (Container, New_Item) =>

          --  Elements are preserved modulo equivalence

          Model (Container)
          = Model (Container)'Old

            --  Cursors are preserved

          and Positions (Container) = Positions (Container)'Old
          and
            E.Equal_Except
              (Elements (Container)'Old,
               Elements (Container),
               P.Get (Positions (Container), Find (Container, New_Item))),

        --  Otherwise, New_Item is inserted in Container

        others                         =>
          Length (Container) = Length (Container)'Old + 1

          --  Other elements are preserved

          and Model (Container)'Old <= Model (Container)
          and
            M.Included_Except
              (Model (Container), Model (Container)'Old, New_Item)

          --  Mapping from cursors to elements is preserved

          and
            Mapping_Preserved
              (E_Left  => Elements (Container)'Old,
               E_Right => Elements (Container),
               P_Left  => Positions (Container)'Old,
               P_Right => Positions (Container))
          and
            P.Keys_Included_Except
              (Positions (Container),
               Positions (Container)'Old,
               Find (Container, New_Item)));

   --  Replaces the element equivalent to New_Item with New_Item
   procedure Replace (Container : in out Set; New_Item : Element_Type)
   with
     Global => null,
     Pre    => Contains (Container, New_Item),
     Post   =>
       Model (Container) = Model (Container)'Old
       and Contains (Container, New_Item)
       and Positions (Container) = Positions (Container)'Old
       and
         Element_Logic_Equal
           (Element (Container, Find (Container, New_Item)),
            E.Copy_Element (New_Item))
       and
         E.Equal_Except
           (Elements (Container)'Old,
            Elements (Container),
            P.Get (Positions (Container), Find (Container, New_Item)));

private

   --  Returns the hash bucket index for element X with the given Modulus
   function Find_Bucket
     (X : Element_Type; Modulus : Hash_Type) return Hash_Type
   with Pre => Modulus /= 0, Post => Find_Bucket'Result in 1 .. Modulus;

   --  Proves that equivalent elements hash to the same bucket
   procedure Lemma_Equivalent_Elements_Find_Bucket
     (X, Y : Element_Type; Modulus : Hash_Type)
   with
     Ghost,
     Pre  => Modulus /= 0,
     Post =>
       (if Equivalent_Elements (X, Y)
        then Find_Bucket (X, Modulus) = Find_Bucket (Y, Modulus));

   type Relaxed_Element is record
      V : Element_Type;
   end record
   with Relaxed_Initialization;

   type Node_Type is record
      Element     : Relaxed_Element;
      Next        : Count_Type := 0;
      Has_Element : Boolean := False;
   end record;

   type Nodes_Type_Base is array (Positive_Count_Type range <>) of Node_Type;

   subtype Nodes_Type is Nodes_Type_Base (1 .. <>)
   with
     Predicate =>
       Nodes_Type'Last >= 0
       and then (for all C of Nodes_Type => C.Next <= Nodes_Type'Last);

   type Buckets_Type is array (Hash_Type range 1 .. <>) of Count_Type;

   type Set
     (Capacity : Count_Type;
      Modulus  : Positive_Hash_Type)
   is record
      Length  : Count_Type := 0;
      Free    : Count_Type'Base := -1;
      Nodes   : Nodes_Type (1 .. Capacity);
      Buckets : Buckets_Type (1 .. Modulus) := (others => 0);
   end record
   with
     Predicate      =>
       Length in 0 .. Capacity
       and then
         (if Capacity = 0 then Free = -1 else Free in -Capacity .. Capacity)
       and then (for all B of Set.Buckets => B <= Capacity),
     Type_Invariant => Invariant (Set);

   function Default_Init (S : Set) return Boolean
   is ((for all B of S.Buckets => B = 0)
       and S.Free = -1
       and S.Length = 0
       and (for all I in 1 .. S.Capacity => not S.Nodes (I).Has_Element));

   --  Full structural invariant of the set representation; used in the
   --  Type_Invariant.
   function Invariant (S : Set) return Boolean
   with Ghost;

end Data_Structure;
