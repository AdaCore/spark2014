------------------------------------------------------------------------------
--                                                                          --
--                        SPARK LIBRARY COMPONENTS                          --
--                                                                          --
--              SPARK.CONTAINERS.FORMAL.UNBOUNDED_ORDERED_MAPS              --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--          Copyright (C) 2022-2022, Free Software Foundation, Inc.         --
--                                                                          --
-- SPARK is free software;  you can  redistribute it and/or modify it under --
-- terms of the  GNU General Public License as published  by the Free Soft- --
-- ware  Foundation;  either version 3,  or (at your option) any later ver- --
-- sion. SPARK is distributed in the hope that it will be useful, but WITH- --
-- OUT ANY WARRANTY;  without even the  implied warranty of MERCHANTABILITY --
-- or FITNESS FOR A PARTICULAR PURPOSE.                                     --
--                                                                          --
-- As a special exception under Section 7 of GPL version 3, you are granted --
-- additional permissions described in the GCC Runtime Library Exception,   --
-- version 3.1, as published by the Free Software Foundation.               --
--                                                                          --
-- You should have received a copy of the GNU General Public License and    --
-- a copy of the GCC Runtime Library Exception along with this program;     --
-- see the files COPYING3 and COPYING.RUNTIME respectively.  If not, see    --
-- <http://www.gnu.org/licenses/>.                                          --
--                                                                          --
------------------------------------------------------------------------------

--  Iteration over maps is done using the Iterable aspect, which is SPARK
--  compatible. "For of" iteration ranges over keys instead of elements.

with SPARK.Containers.Functional.Vectors;
with SPARK.Containers.Functional.Maps;
with SPARK.Containers.Parameter_Checks;
with SPARK.Containers.Types; use SPARK.Containers.Types;

private with Ada.Containers.Red_Black_Trees;
private with SPARK.Containers.Formal.Holders;

generic
   type Key_Type (<>) is private;
   type Element_Type (<>) is private;

   with function "<" (Left, Right : Key_Type) return Boolean is <>;
   with function "=" (Left, Right : Element_Type) return Boolean is <>;

   --  Ghost lemmas used to prove that "=" is an equivalence relation

   with procedure Eq_Reflexive (X : Element_Type) is null
     with Ghost;
   with procedure Eq_Symmetric (X, Y : Element_Type) is null
     with Ghost;
   with procedure Eq_Transitive (X, Y, Z : Element_Type) is null
     with Ghost;

   --  Ghost lemmas used to prove that "<" is a strict weak ordering
   --  relationship.

   with procedure Lt_Irreflexive (X : Key_Type) is null
     with Ghost;
   with procedure Lt_Asymmetric (X, Y : Key_Type) is null
     with Ghost;
   with procedure Lt_Transitive (X, Y, Z : Key_Type) is null
     with Ghost;
   with procedure Lt_Order (X, Y, Z : Key_Type) is null
     with Ghost;

package SPARK.Containers.Formal.Unbounded_Ordered_Maps with
  SPARK_Mode,
  Annotate => (GNATprove, Always_Return)
is

   --  Contracts in this unit are meant for analysis only, not for run-time
   --  checking.

   pragma Assertion_Policy (Pre => Ignore);
   pragma Assertion_Policy (Post => Ignore);
   pragma Assertion_Policy (Contract_Cases => Ignore);
   pragma Annotate (CodePeer, Skip_Analysis);

   function Equivalent_Keys (Left, Right : Key_Type) return Boolean with
     Global => null,
     Post   =>
       Equivalent_Keys'Result = (not (Left < Right) and not (Right < Left));
   pragma Annotate (GNATprove, Inline_For_Proof, Equivalent_Keys);

   type Map is private with
     Iterable => (First       => First,
                  Next        => Next,
                  Has_Element => Has_Element,
                  Element     => Key),
     Default_Initial_Condition => Is_Empty (Map);

   type Cursor is record
      Node : Count_Type;
   end record;

   No_Element : constant Cursor := (Node => 0);

   Empty_Map : constant Map;

   function Length (Container : Map) return Count_Type with
     Global => null;

   pragma Unevaluated_Use_Of_Old (Allow);

   package Formal_Model with Ghost is

      --  Logical equality cannot be safely executed on most element or key
      --  types. Thus, this package should only be instantiated with ghost code
      --  disabled. This is enforced by having a special imported procedure
      --  Check_Or_Fail that will lead to link-time errors otherwise.

      function Key_Logic_Equal (Left, Right : Key_Type) return Boolean with
        Global => null,
        Annotate => (GNATprove, Logical_Equal);

      function Element_Logic_Equal (Left, Right : Element_Type) return Boolean
      with
        Global => null,
        Annotate => (GNATprove, Logical_Equal);

      --------------------------
      -- Instantiation Checks --
      --------------------------

      package Eq_Checks is new
        SPARK.Containers.Parameter_Checks.Equivalence_Checks
          (T                   => Element_Type,
           Eq                  => "=",
           Param_Eq_Reflexive  => Eq_Reflexive,
           Param_Eq_Symmetric  => Eq_Symmetric,
           Param_Eq_Transitive => Eq_Transitive);
      --  Check that the actual parameter for "=" is an equivalence relation

      package Lift_Eq is new
        SPARK.Containers.Parameter_Checks.Lift_Eq_Reflexive
          (T                  => Element_Type,
           "="                => Element_Logic_Equal,
           Eq                 => "=",
           Param_Eq_Reflexive => Eq_Checks.Eq_Reflexive);

      package Lt_Checks is new
        SPARK.Containers.Parameter_Checks.Strict_Weak_Order_Checks
          (T                    => Key_Type,
           "<"                  => "<",
           Param_Lt_Irreflexive => Lt_Irreflexive,
           Param_Lt_Asymmetric  => Lt_Asymmetric,
           Param_Lt_Transitive  => Lt_Transitive,
           Param_Lt_Order       => Lt_Order);
      --  Check that "<" is a strict weak ordering relationship

      package Lift_Equivalent_Keys is new
        SPARK.Containers.Parameter_Checks.Lift_Eq_Reflexive
          (T                  => Key_Type,
           "="                => Key_Logic_Equal,
           Eq                 => Equivalent_Keys,
           Param_Eq_Reflexive => Lt_Checks.Eq_Reflexive);

      ------------------
      -- Formal Model --
      ------------------

      subtype Positive_Count_Type is Count_Type range 1 .. Count_Type'Last;

      package M is new SPARK.Containers.Functional.Maps
        (Element_Type                   => Element_Type,
         Key_Type                       => Key_Type,
         Equivalent_Keys                => Equivalent_Keys,
         "="                            => Element_Logic_Equal,
         Equivalent_Elements            => "=",
         Equivalent_Elements_Reflexive  => Lift_Eq.Eq_Reflexive,
         Equivalent_Elements_Symmetric  => Eq_Checks.Eq_Symmetric,
         Equivalent_Elements_Transitive => Eq_Checks.Eq_Transitive,
         Equivalent_Keys_Reflexive      => Lt_Checks.Eq_Reflexive,
         Equivalent_Keys_Symmetric      => Lt_Checks.Eq_Symmetric,
         Equivalent_Keys_Transitive     => Lt_Checks.Eq_Transitive);

      function "="
        (Left  : M.Map;
         Right : M.Map) return Boolean renames M."=";

      function "<="
        (Left  : M.Map;
         Right : M.Map) return Boolean renames M."<=";

      package K is new SPARK.Containers.Functional.Vectors
        (Element_Type                   => Key_Type,
         Index_Type                     => Positive_Count_Type,
         "="                            => Key_Logic_Equal,
         Equivalent_Elements            => Equivalent_Keys,
         Equivalent_Elements_Reflexive  => Lift_Equivalent_Keys.Eq_Reflexive,
         Equivalent_Elements_Symmetric  => Lt_Checks.Eq_Symmetric,
         Equivalent_Elements_Transitive => Lt_Checks.Eq_Transitive);

      function "="
        (Left  : K.Sequence;
         Right : K.Sequence) return Boolean renames K."=";

      function "<"
        (Left  : K.Sequence;
         Right : K.Sequence) return Boolean renames K."<";

      function "<="
        (Left  : K.Sequence;
         Right : K.Sequence) return Boolean renames K."<=";

      function K_Bigger_Than_Range
        (Container : K.Sequence;
         Fst       : Positive_Count_Type;
         Lst       : Count_Type;
         Key       : Key_Type) return Boolean
      with
        Global => null,
        Pre    => Lst <= K.Length (Container),
        Post   =>
          K_Bigger_Than_Range'Result =
            (for all I in Fst .. Lst => K.Get (Container, I) < Key);
      pragma Annotate (GNATprove, Inline_For_Proof, K_Bigger_Than_Range);

      function K_Smaller_Than_Range
        (Container : K.Sequence;
         Fst       : Positive_Count_Type;
         Lst       : Count_Type;
         Key       : Key_Type) return Boolean
      with
        Global => null,
        Pre    => Lst <= K.Length (Container),
        Post   =>
          K_Smaller_Than_Range'Result =
            (for all I in Fst .. Lst => Key < K.Get (Container, I));
      pragma Annotate (GNATprove, Inline_For_Proof, K_Smaller_Than_Range);

      function K_Is_Find
        (Container : K.Sequence;
         Key       : Key_Type;
         Position  : Count_Type) return Boolean
      with
        Global => null,
        Pre    => Position - 1 <= K.Length (Container),
        Post   =>
          K_Is_Find'Result =
             ((if Position > 0 then
                  K_Bigger_Than_Range (Container, 1, Position - 1, Key))

            and
              (if Position < K.Length (Container) then
                  K_Smaller_Than_Range
                    (Container,
                     Position + 1,
                     K.Length (Container),
                     Key)));
      pragma Annotate (GNATprove, Inline_For_Proof, K_Is_Find);

      function Find (Container : K.Sequence; Key : Key_Type) return Count_Type
      --  Search for Key in Container

      with
        Global => null,
        Post =>
          (if Find'Result > 0 then
              Find'Result <= K.Length (Container)
                and Equivalent_Keys (Key, K.Get (Container, Find'Result)));

      package P is new SPARK.Containers.Functional.Maps
        (Key_Type                       => Cursor,
         Element_Type                   => Positive_Count_Type,
         Equivalent_Keys                => "=",
         Enable_Handling_Of_Equivalence => False);

      function "="
        (Left  : P.Map;
         Right : P.Map) return Boolean renames P."=";

      function "<="
        (Left  : P.Map;
         Right : P.Map) return Boolean renames P."<=";

      function P_Positions_Shifted
        (Small : P.Map;
         Big   : P.Map;
         Cut   : Positive_Count_Type;
         Count : Count_Type := 1) return Boolean
      with
        Global => null,
        Post   =>
          P_Positions_Shifted'Result =

            --  Big contains all cursors of Small

            (P.Keys_Included (Small, Big)

              --  Cursors located before Cut are not moved, cursors located
              --  after are shifted by Count.

              and (for all I of Small =>
                    (if P.Get (Small, I) < Cut then
                        P.Get (Big, I) = P.Get (Small, I)
                     else
                        P.Get (Big, I) - Count = P.Get (Small, I)))

              --  New cursors of Big (if any) are between Cut and Cut - 1 +
              --  Count.

              and (for all I of Big =>
                    P.Has_Key (Small, I)
                      or P.Get (Big, I) - Count in Cut - Count  .. Cut - 1));

      function Model (Container : Map) return M.Map with
      --  The high-level model of a map is a map from keys to elements. Neither
      --  cursors nor order of elements are represented in this model. Keys are
      --  modeled up to equivalence.

        Ghost,
        Global => null;

      function Keys (Container : Map) return K.Sequence with
      --  The Keys sequence represents the underlying list structure of maps
      --  that is used for iteration. It stores the actual values of keys in
      --  the map. It does not model cursors nor elements.

        Ghost,
        Global => null,
        Post   =>
          K.Length (Keys'Result) = Length (Container)

            --  It only contains keys contained in Model

            and (for all Key of Keys'Result =>
                  M.Has_Key (Model (Container), Key))

            --  It contains all the keys contained in Model

            and (for all Key of Model (Container) =>
                  (Find (Keys'Result, Key) > 0
                    and then Equivalent_Keys
                               (K.Get (Keys'Result, Find (Keys'Result, Key)),
                                Key)))

            --  It is sorted in increasing order

            and (for all I in 1 .. Length (Container) =>
                  Find (Keys'Result, K.Get (Keys'Result, I)) = I
                    and K_Is_Find (Keys'Result, K.Get (Keys'Result, I), I));
      pragma Annotate (GNATprove, Iterable_For_Proof, "Model", Keys);

      function Positions (Container : Map) return P.Map with
      --  The Positions map is used to model cursors. It only contains valid
      --  cursors and maps them to their position in the container.

        Ghost,
        Global => null,
        Post   =>
          not P.Has_Key (Positions'Result, No_Element)

            --  Positions of cursors are smaller than the container's length.

            and then
              (for all I of Positions'Result =>
                P.Get (Positions'Result, I) in 1 .. Length (Container)

            --  No two cursors have the same position. Note that we do not
            --  state that there is a cursor in the map for each position, as
            --  it is rarely needed.

            and then
              (for all J of Positions'Result =>
                (if P.Get (Positions'Result, I) = P.Get (Positions'Result, J)
                 then I = J)));

      procedure Lift_Abstraction_Level (Container : Map) with
        --  Lift_Abstraction_Level is a ghost procedure that does nothing but
        --  assume that we can access the same elements by iterating over
        --  positions or cursors.
        --  This information is not generally useful except when switching from
        --  a low-level, cursor-aware view of a container, to a high-level,
        --  position-based view.

        Ghost,
        Global => null,
        Post   =>
          (for all Key of Keys (Container) =>
            (for some I of Positions (Container) =>
               Key_Logic_Equal
                 (K.Get (Keys (Container), P.Get (Positions (Container), I)),
                  Key)));

      function Contains
        (C : M.Map;
         K : Key_Type) return Boolean renames M.Has_Key;
      --  To improve readability of contracts, we rename the function used to
      --  search for a key in the model to Contains.

      function Element
        (C : M.Map;
         K : Key_Type) return Element_Type renames M.Get;
      --  To improve readability of contracts, we rename the function used to
      --  access an element in the model to Element.
   end Formal_Model;
   use Formal_Model;

   function "=" (Left, Right : Map) return Boolean with
     Global => null,
     Post   => "="'Result = (M.Equivalent_Maps (Model (Left), Model (Right)));

   function Is_Empty (Container : Map) return Boolean with
     Global => null,
     Post   =>
       Is_Empty'Result = M.Is_Empty (Model (Container))
         and (Is_Empty'Result = (Length (Container) = 0));

   procedure Clear (Container : in out Map) with
     Global => null,
     Post   => Length (Container) = 0 and M.Is_Empty (Model (Container));

   procedure Assign (Target : in out Map; Source : Map) with
     Global => null,
     Post   =>
       Model (Target) = Model (Source)
         and Keys (Target) = Keys (Source)
         and Length (Source) = Length (Target);

   function Copy (Source : Map) return Map with
     Global => null,
     Post   =>
       Model (Copy'Result) = Model (Source)
         and Keys (Copy'Result) = Keys (Source)
         and Positions (Copy'Result) = Positions (Source);

   function Key (Container : Map; Position : Cursor) return Key_Type with
     Global => null,
     Pre    => Has_Element (Container, Position),
     Post   =>
       Key'Result =
         K.Get (Keys (Container), P.Get (Positions (Container), Position));
   pragma Annotate (GNATprove, Inline_For_Proof, Key);

   function Element
     (Container : Map;
      Position  : Cursor) return Element_Type
   with
     Global => null,
     Pre    => Has_Element (Container, Position),
     Post   =>
       Element'Result = Element (Model (Container), Key (Container, Position));
   pragma Annotate (GNATprove, Inline_For_Proof, Element);

   procedure Replace_Element
     (Container : in out Map;
      Position  : Cursor;
      New_Item  : Element_Type)
   with
     Global => null,
     Pre    => Has_Element (Container, Position),
     Post   =>

       --  Order of keys and cursors is preserved

       Keys (Container) = Keys (Container)'Old
         and Positions (Container) = Positions (Container)'Old

         --  New_Item is now associated with the key at position Position in
         --  Container.

         and Element_Logic_Equal (Element (Container, Position), New_Item)

         --  Elements associated with other keys are preserved

         and M.Same_Keys (Model (Container), Model (Container)'Old)
         and M.Elements_Equal_Except
               (Model (Container),
                Model (Container)'Old,
                Key (Container, Position));

   function At_End
     (E : not null access constant Map) return not null access constant Map
   is (E)
   with Ghost,
     Annotate => (GNATprove, At_End_Borrow);

   function At_End
     (E : access constant Element_Type) return access constant Element_Type
   is (E)
   with Ghost,
     Annotate => (GNATprove, At_End_Borrow);

   function Constant_Reference
     (Container : Map;
      Position  : Cursor) return not null access constant Element_Type
   with
     Global => null,
     Pre    => Has_Element (Container, Position),
     Post   =>
       Element_Logic_Equal
         (Constant_Reference'Result.all,
          Element (Model (Container), Key (Container, Position)));

   function Reference
     (Container : not null access Map;
      Position  : Cursor) return not null access Element_Type
   with
     Global => null,
     Pre    => Has_Element (Container.all, Position),
     Post   =>

       --  Order of keys and cursors is preserved

       Keys (At_End (Container).all) = Keys (Container.all)
         and Positions (At_End (Container).all) = Positions (Container.all)

         --  The value designated by the result of Reference is now associated
         --  with the key at position Position in Container.

         and Element_Logic_Equal
               (Element (At_End (Container).all, Position),
                At_End (Reference'Result).all)

         --  Elements associated with other keys are preserved

         and M.Same_Keys
               (Model (At_End (Container).all),
                Model (Container.all))
         and M.Elements_Equal_Except
               (Model (At_End (Container).all),
                Model (Container.all),
                Key (At_End (Container).all, Position));

   function Constant_Reference
     (Container : Map;
      Key       : Key_Type) return not null access constant Element_Type
   with
     Global => null,
     Pre    => Contains (Container, Key),
     Post   =>
       Element_Logic_Equal
         (Constant_Reference'Result.all, Element (Model (Container), Key));

   function Reference
     (Container : not null access Map;
      Key       : Key_Type) return not null access Element_Type
   with
     Global => null,
     Pre    => Contains (Container.all, Key),
     Post   =>

       --  Order of keys and cursors is preserved

       Keys (At_End (Container).all) = Keys (Container.all)
         and Positions (At_End (Container).all) = Positions (Container.all)

         --  The value designated by the result of Reference is now associated
         --  with Key in Container.

         and Element_Logic_Equal
               (Element (Model (At_End (Container).all), Key),
                At_End (Reference'Result).all)

         --  Elements associated with other keys are preserved

         and M.Same_Keys
               (Model (At_End (Container).all),
                Model (Container.all))
         and M.Elements_Equal_Except
               (Model (At_End (Container).all),
                Model (Container.all),
                Key);

   procedure Move (Target : in out Map; Source : in out Map) with
     Global => null,
     Post   =>
       Model (Target) = Model (Source)'Old
         and Keys (Target) = Keys (Source)'Old
         and Length (Source)'Old = Length (Target)
         and Length (Source) = 0;

   procedure Insert
     (Container : in out Map;
      Key       : Key_Type;
      New_Item  : Element_Type;
      Position  : out Cursor;
      Inserted  : out Boolean)
   with
     Global         => null,
     Pre            =>
       Length (Container) < Count_Type'Last or Contains (Container, Key),
     Post           =>
       Contains (Container, Key)
         and Has_Element (Container, Position)
         and Equivalent_Keys
               (Formal.Unbounded_Ordered_Maps.Key
                  (Container, Position), Key)
         and K_Is_Find
               (Keys (Container),
                Key,
                P.Get (Positions (Container), Position)),
     Contract_Cases =>

       --  If Key is already in Container, it is not modified and Inserted is
       --  set to False.

       (Contains (Container, Key) =>
          not Inserted
            and Model (Container) = Model (Container)'Old
            and Keys (Container) = Keys (Container)'Old
            and Positions (Container) = Positions (Container)'Old,

        --  Otherwise, Key is inserted in Container and Inserted is set to True

        others =>
          Inserted
            and Length (Container) = Length (Container)'Old + 1

            --  Key now maps to New_Item

            and Key_Logic_Equal
                  (Formal.Unbounded_Ordered_Maps.Key (Container, Position),
                   Key)
            and Element_Logic_Equal
                  (Element (Model (Container), Key), New_Item)

            --  Other mappings are preserved

            and Model (Container)'Old <= Model (Container)
            and M.Keys_Included_Except
                  (Model (Container),
                   Model (Container)'Old,
                   Key)

            --  The keys of Container located before Position are preserved

            and K.Range_Equal
                  (Left  => Keys (Container)'Old,
                   Right => Keys (Container),
                   Fst   => 1,
                   Lst   => P.Get (Positions (Container), Position) - 1)

            --  Other keys are shifted by 1

            and K.Range_Shifted
                  (Left   => Keys (Container)'Old,
                   Right  => Keys (Container),
                   Fst    => P.Get (Positions (Container), Position),
                   Lst    => Length (Container)'Old,
                   Offset => 1)

            --  A new cursor has been inserted at position Position in
            --  Container.

            and P_Positions_Shifted
                  (Positions (Container)'Old,
                   Positions (Container),
                   Cut => P.Get (Positions (Container), Position)));

   procedure Insert
     (Container : in out Map;
      Key       : Key_Type;
      New_Item  : Element_Type)
   with
     Global => null,
     Pre    =>
       Length (Container) < Count_Type'Last
         and then (not Contains (Container, Key)),
     Post   =>
       Length (Container) = Length (Container)'Old + 1
         and Contains (Container, Key)

         --  Key now maps to New_Item

         and Key_Logic_Equal
               (K.Get (Keys (Container), Find (Keys (Container), Key)), Key)
         and Element_Logic_Equal (Element (Model (Container), Key), New_Item)

         --  Other mappings are preserved

         and Model (Container)'Old <= Model (Container)
         and M.Keys_Included_Except
               (Model (Container),
                Model (Container)'Old,
                Key)

         --  The keys of Container located before Key are preserved

         and K.Range_Equal
               (Left  => Keys (Container)'Old,
                Right => Keys (Container),
                Fst   => 1,
                Lst   => Find (Keys (Container), Key) - 1)

         --  Other keys are shifted by 1

         and K.Range_Shifted
               (Left   => Keys (Container)'Old,
                Right  => Keys (Container),
                Fst    => Find (Keys (Container), Key),
                Lst    => Length (Container)'Old,
                Offset => 1)

         --  A new cursor has been inserted in Container

         and P_Positions_Shifted
               (Positions (Container)'Old,
                Positions (Container),
                Cut => Find (Keys (Container), Key));

   procedure Include
     (Container : in out Map;
      Key       : Key_Type;
      New_Item  : Element_Type)
   with
     Global         => null,
     Pre            =>
       Length (Container) < Count_Type'Last or Contains (Container, Key),
     Post           =>
       Contains (Container, Key)
         and Element_Logic_Equal (Element (Container, Key), New_Item),
     Contract_Cases =>

       --  If Key is already in Container, Key is mapped to New_Item

       (Contains (Container, Key) =>

          --  Cursors are preserved

          Positions (Container) = Positions (Container)'Old

            --  The key equivalent to Key in Container is replaced by Key

            and Key_Logic_Equal
                  (K.Get (Keys (Container), Find (Keys (Container), Key)), Key)

            and K.Equal_Except
                  (Keys (Container)'Old,
                   Keys (Container),
                   Find (Keys (Container), Key))

            --  Elements associated with other keys are preserved

            and M.Same_Keys (Model (Container), Model (Container)'Old)
            and M.Elements_Equal_Except
                  (Model (Container),
                   Model (Container)'Old,
                   Key),

        --  Otherwise, Key is inserted in Container

        others =>
          Length (Container) = Length (Container)'Old + 1

            --  Other mappings are preserved

            and Model (Container)'Old <= Model (Container)
            and M.Keys_Included_Except
                  (Model (Container),
                   Model (Container)'Old,
                   Key)

            --  Key is inserted in Container

            and Key_Logic_Equal
                  (K.Get (Keys (Container), Find (Keys (Container), Key)), Key)

            --  The keys of Container located before Key are preserved

            and K.Range_Equal
                  (Left  => Keys (Container)'Old,
                   Right => Keys (Container),
                   Fst   => 1,
                   Lst   => Find (Keys (Container), Key) - 1)

            --  Other keys are shifted by 1

            and K.Range_Shifted
                  (Left   => Keys (Container)'Old,
                   Right  => Keys (Container),
                   Fst    => Find (Keys (Container), Key),
                   Lst    => Length (Container)'Old,
                   Offset => 1)

            --  A new cursor has been inserted in Container

            and P_Positions_Shifted
                  (Positions (Container)'Old,
                   Positions (Container),
                   Cut => Find (Keys (Container), Key)));

   procedure Replace
     (Container : in out Map;
      Key       : Key_Type;
      New_Item  : Element_Type)
   with
     Global => null,
     Pre    => Contains (Container, Key),
     Post   =>

       --  Cursors are preserved

       Positions (Container) = Positions (Container)'Old

         --  The key equivalent to Key in Container is replaced by Key

         and Key_Logic_Equal
              (K.Get (Keys (Container), Find (Keys (Container), Key)), Key)
         and K.Equal_Except
              (Keys (Container)'Old,
               Keys (Container),
               Find (Keys (Container), Key))

         --  New_Item is now associated with the Key in Container

         and Element_Logic_Equal (Element (Model (Container), Key), New_Item)

         --  Elements associated with other keys are preserved

         and M.Same_Keys (Model (Container), Model (Container)'Old)
         and M.Elements_Equal_Except
               (Model (Container),
                Model (Container)'Old,
                Key);

   procedure Exclude (Container : in out Map; Key : Key_Type) with
     Global         => null,
     Post           => not Contains (Container, Key),
     Contract_Cases =>

       --  If Key is not in Container, nothing is changed

       (not Contains (Container, Key) =>
          Model (Container) = Model (Container)'Old
            and Keys (Container) = Keys (Container)'Old
            and Positions (Container) = Positions (Container)'Old,

        --  Otherwise, Key is removed from Container

        others =>
          Length (Container) = Length (Container)'Old - 1

            --  Other mappings are preserved

            and Model (Container) <= Model (Container)'Old
            and M.Keys_Included_Except
                  (Model (Container)'Old,
                   Model (Container),
                   Key)

            --  The keys of Container located before Key are preserved

            and K.Range_Equal
                  (Left  => Keys (Container)'Old,
                   Right => Keys (Container),
                   Fst   => 1,
                   Lst   => Find (Keys (Container), Key)'Old - 1)

            --  The keys located after Key are shifted by 1

            and K.Range_Shifted
                  (Left   => Keys (Container),
                   Right  => Keys (Container)'Old,
                   Fst    => Find (Keys (Container), Key)'Old,
                   Lst    => Length (Container),
                   Offset => 1)

            --  A cursor has been removed from Container

            and P_Positions_Shifted
                  (Positions (Container),
                   Positions (Container)'Old,
                   Cut   => Find (Keys (Container), Key)'Old));

   procedure Delete (Container : in out Map; Key : Key_Type) with
     Global => null,
     Pre    => Contains (Container, Key),
     Post   =>
       Length (Container) = Length (Container)'Old - 1

         --  Key is no longer in Container

         and not Contains (Container, Key)

         --  Other mappings are preserved

         and Model (Container) <= Model (Container)'Old
         and M.Keys_Included_Except
               (Model (Container)'Old,
                Model (Container),
                Key)

         --  The keys of Container located before Key are preserved

         and K.Range_Equal
               (Left  => Keys (Container)'Old,
                Right => Keys (Container),
                Fst   => 1,
                Lst   => Find (Keys (Container), Key)'Old - 1)

         --  The keys located after Key are shifted by 1

         and K.Range_Shifted
               (Left   => Keys (Container),
                Right  => Keys (Container)'Old,
                Fst    => Find (Keys (Container), Key)'Old,
                Lst    => Length (Container),
                Offset => 1)

         --  A cursor has been removed from Container

         and P_Positions_Shifted
               (Positions (Container),
                Positions (Container)'Old,
                Cut   => Find (Keys (Container), Key)'Old);

   procedure Delete (Container : in out Map; Position : in out Cursor) with
     Global  => null,
     Depends => (Container =>+ Position, Position => null),
     Pre     => Has_Element (Container, Position),
     Post    =>
       Position = No_Element
         and Length (Container) = Length (Container)'Old - 1

         --  The key at position Position is no longer in Container

         and not Contains (Container, Key (Container, Position)'Old)
         and not P.Has_Key (Positions (Container), Position'Old)

         --  Other mappings are preserved

         and Model (Container) <= Model (Container)'Old
         and M.Keys_Included_Except
               (Model (Container)'Old,
                Model (Container),
                Key (Container, Position)'Old)

         --  The keys of Container located before Position are preserved.

         and K.Range_Equal
               (Left  => Keys (Container)'Old,
                Right => Keys (Container),
                Fst   => 1,
                Lst   => P.Get (Positions (Container)'Old, Position'Old) - 1)

         --  The keys located after Position are shifted by 1

         and K.Range_Shifted
               (Left   => Keys (Container),
                Right  => Keys (Container)'Old,
                Fst    => P.Get (Positions (Container)'Old, Position'Old),
                Lst    => Length (Container),
                Offset => 1)

         --  Position has been removed from Container

         and P_Positions_Shifted
               (Positions (Container),
                Positions (Container)'Old,
                Cut   => P.Get (Positions (Container)'Old, Position'Old));

   procedure Delete_First (Container : in out Map) with
     Global         => null,
     Contract_Cases =>
       (Length (Container) = 0 => Length (Container) = 0,
        others =>
          Length (Container) = Length (Container)'Old - 1

            --  The first key has been removed from Container

            and not Contains (Container, First_Key (Container)'Old)

            --  Other mappings are preserved

            and Model (Container) <= Model (Container)'Old
            and M.Keys_Included_Except
                  (Model (Container)'Old,
                   Model (Container),
                    First_Key (Container)'Old)

            --  Other keys are shifted by 1

            and K.Range_Shifted
                  (Left   => Keys (Container),
                   Right  => Keys (Container)'Old,
                   Fst    => 1,
                   Lst    => Length (Container),
                   Offset => 1)

            --  First has been removed from Container

            and P_Positions_Shifted
                  (Positions (Container),
                   Positions (Container)'Old,
                   Cut   => 1));

   procedure Delete_Last (Container : in out Map) with
     Global         => null,
     Contract_Cases =>
       (Length (Container) = 0 => Length (Container) = 0,
        others =>
          Length (Container) = Length (Container)'Old - 1

            --  The last key has been removed from Container

            and not Contains (Container, Last_Key (Container)'Old)

            --  Other mappings are preserved

            and Model (Container) <= Model (Container)'Old
            and M.Keys_Included_Except
                  (Model (Container)'Old,
                   Model (Container),
                   Last_Key (Container)'Old)

            --  Others keys of Container are preserved

            and K.Range_Equal
                  (Left  => Keys (Container)'Old,
                   Right => Keys (Container),
                   Fst   => 1,
                   Lst   => Length (Container))

            --  Last cursor has been removed from Container

            and Positions (Container) <= Positions (Container)'Old);

   function First (Container : Map) return Cursor with
     Global         => null,
     Contract_Cases =>
       (Length (Container) = 0 =>
          First'Result = No_Element,

        others =>
          Has_Element (Container, First'Result)
            and P.Get (Positions (Container), First'Result) = 1);

   function First_Element (Container : Map) return Element_Type with
     Global => null,
     Pre    => not Is_Empty (Container),
     Post   =>
       First_Element'Result =
         Element (Model (Container), First_Key (Container));

   function First_Key (Container : Map) return Key_Type with
     Global => null,
     Pre    => not Is_Empty (Container),
     Post   =>
       First_Key'Result = K.Get (Keys (Container), 1)
         and K_Smaller_Than_Range
               (Keys (Container), 2, Length (Container), First_Key'Result);

   function Last (Container : Map) return Cursor with
     Global         => null,
     Contract_Cases =>
       (Length (Container) = 0 =>
          Last'Result = No_Element,

        others =>
          Has_Element (Container, Last'Result)
            and P.Get (Positions (Container), Last'Result) =
                  Length (Container));

   function Last_Element (Container : Map) return Element_Type with
     Global => null,
     Pre    => not Is_Empty (Container),
     Post   =>
       Last_Element'Result = Element (Model (Container), Last_Key (Container));

   function Last_Key (Container : Map) return Key_Type with
     Global => null,
     Pre    => not Is_Empty (Container),
     Post   =>
       Last_Key'Result = K.Get (Keys (Container), Length (Container))
         and K_Bigger_Than_Range
               (Keys (Container), 1, Length (Container) - 1, Last_Key'Result);

   function Next (Container : Map; Position : Cursor) return Cursor with
     Global         => null,
     Pre            =>
       Has_Element (Container, Position) or else Position = No_Element,
     Contract_Cases =>
       (Position = No_Element
          or else P.Get (Positions (Container), Position) = Length (Container)
        =>
          Next'Result = No_Element,

        others =>
          Has_Element (Container, Next'Result)
            and then P.Get (Positions (Container), Next'Result) =
                     P.Get (Positions (Container), Position) + 1);

   procedure Next (Container : Map; Position : in out Cursor) with
     Global         => null,
     Pre            =>
       Has_Element (Container, Position) or else Position = No_Element,
     Contract_Cases =>
       (Position = No_Element
          or else P.Get (Positions (Container), Position) = Length (Container)
        =>
          Position = No_Element,

        others =>
          Has_Element (Container, Position)
            and then P.Get (Positions (Container), Position) =
                     P.Get (Positions (Container), Position'Old) + 1);

   function Previous (Container : Map; Position : Cursor) return Cursor with
     Global         => null,
     Pre            =>
       Has_Element (Container, Position) or else Position = No_Element,
     Contract_Cases =>
       (Position = No_Element
          or else P.Get (Positions (Container), Position) = 1
        =>
          Previous'Result = No_Element,

        others =>
          Has_Element (Container, Previous'Result)
            and then P.Get (Positions (Container), Previous'Result) =
                     P.Get (Positions (Container), Position) - 1);

   procedure Previous (Container : Map; Position : in out Cursor) with
     Global         => null,
     Pre            =>
       Has_Element (Container, Position) or else Position = No_Element,
     Contract_Cases =>
       (Position = No_Element
          or else P.Get (Positions (Container), Position) = 1
        =>
          Position = No_Element,

        others =>
          Has_Element (Container, Position)
            and then P.Get (Positions (Container), Position) =
                     P.Get (Positions (Container), Position'Old) - 1);

   function Find (Container : Map; Key : Key_Type) return Cursor with
     Global         => null,
     Contract_Cases =>

       --  If Key is not contained in Container, Find returns No_Element

       (not Contains (Model (Container), Key) =>
          not P.Has_Key (Positions (Container), Find'Result)
            and Find'Result = No_Element,

        --  Otherwise, Find returns a valid cursor in Container

        others =>
          P.Has_Key (Positions (Container), Find'Result)
            and P.Get (Positions (Container), Find'Result) =
                Find (Keys (Container), Key)

            --  The key designated by the result of Find is Key

            and Equivalent_Keys
                  (Formal.Unbounded_Ordered_Maps.Key
                     (Container, Find'Result), Key));

   function Element (Container : Map; Key : Key_Type) return Element_Type with
     Global => null,
     Pre    => Contains (Container, Key),
     Post   => Element'Result = Element (Model (Container), Key);
   pragma Annotate (GNATprove, Inline_For_Proof, Element);

   function Floor (Container : Map; Key : Key_Type) return Cursor with
     Global         => null,
     Contract_Cases =>
       (Length (Container) = 0 or else Key < First_Key (Container) =>
          Floor'Result = No_Element,

        others =>
          Has_Element (Container, Floor'Result)
            and not (Key < K.Get (Keys (Container),
                                  P.Get (Positions (Container), Floor'Result)))
            and K_Is_Find
                  (Keys (Container),
                   Key,
                   P.Get (Positions (Container), Floor'Result)));

   function Ceiling (Container : Map; Key : Key_Type) return Cursor with
     Global         => null,
     Contract_Cases =>
       (Length (Container) = 0 or else Last_Key (Container) < Key =>
          Ceiling'Result = No_Element,
        others =>
          Has_Element (Container, Ceiling'Result)
            and not (K.Get
                       (Keys (Container),
                        P.Get (Positions (Container), Ceiling'Result)) < Key)
            and K_Is_Find
                  (Keys (Container),
                   Key,
                   P.Get (Positions (Container), Ceiling'Result)));

   function Contains (Container : Map; Key : Key_Type) return Boolean with
     Global => null,
     Post   => Contains'Result = Contains (Model (Container), Key);
   pragma Annotate (GNATprove, Inline_For_Proof, Contains);

   function Has_Element (Container : Map; Position : Cursor) return Boolean
   with
     Global => null,
     Post   =>
       Has_Element'Result = P.Has_Key (Positions (Container), Position);
   pragma Annotate (GNATprove, Inline_For_Proof, Has_Element);

private
   pragma SPARK_Mode (Off);

   pragma Inline (Next);
   pragma Inline (Previous);

   --  Defines the Holder type

   package Element_Holder_Types is new Holders (Element_Type);
   package EHT renames Element_Holder_Types;

   package Key_Holder_Types is new Holders (Key_Type);
   package KHT renames Key_Holder_Types;

   --  Defines the actual Map

   subtype Node_Access is Count_Type;

   use Red_Black_Trees;

   type Node_Type is record
      Has_Element : Boolean := False;
      Parent      : Node_Access := 0;
      Left        : Node_Access := 0;
      Right       : Node_Access := 0;
      Color       : Red_Black_Trees.Color_Type := Red;
      K_Holder    : KHT.Holder_Type;
      E_Holder    : EHT.Holder_Type;
   end record;

   package Tree_Types is
     new Ada.Containers.Red_Black_Trees.Generic_Bounded_Tree_Types (Node_Type);

   type Tree_Access is access all Tree_Types.Tree_Type;

   Empty_Tree : aliased Tree_Types.Tree_Type (0);

   type Map is new Ada.Finalization.Controlled
   with record
     Content : not null Tree_Access := Empty_Tree'Access;
   end record;

   overriding procedure Adjust (Container : in out Map);
   --  Makes a copy of Container in order to avoid sharing

   overriding procedure Finalize (Container : in out Map);
   --  Dealocate the Content field if necessary

   Empty_Map : constant Map := (Ada.Finalization.Controlled with others => <>);

end SPARK.Containers.Formal.Unbounded_Ordered_Maps;
