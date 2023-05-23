------------------------------------------------------------------------------
--                                                                          --
--                         SPARK LIBRARY COMPONENTS                         --
--                                                                          --
--                   SPARK.CONTAINERS.FUNCTIONAL.MULTISETS                  --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--          Copyright (C) 2022-2023, Free Software Foundation, Inc.         --
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

package body SPARK.Containers.Functional.Multisets
  with SPARK_Mode =>
#if SPARK_BODY_MODE="On"
  On
#else
  Off
#end if;
is
   use Maps;

   -----------------------
   -- Local Subprograms --
   -----------------------

   function Cardinality_Rec (Container : Maps.Map) return Big_Natural with
   --  Computes recursively the Cardinality - i.e. the sum of the number of
   --  occurences of all the elements - of Container.

     Ghost,
     Global             => null,
     Subprogram_Variant => (Decreases => Maps.Length (Container)),
     Post               =>
       (for all Element of Container =>
          Get (Container, Element) <= Cardinality_Rec'Result);

   ------------------
   -- Local Lemmas --
   ------------------

   procedure Lemma_Eq (M1, M2 : Maps.Map) with
   --  States that if two multisets are equal, then they have the same
   --  cardinality.

     Ghost,
     Pre                => M1 = M2,
     Post               => Cardinality_Rec (M1) = Cardinality_Rec (M2),
     Subprogram_Variant => (Decreases => Length (M1), Decreases => 1);

   procedure Lemma_Remove (M : Maps.Map; K : Element_Type) with
   --  States that if an element is removed from a multiset, then its number of
   --  occurences is removed from the cardinality of this multiset.

     Ghost,
     Subprogram_Variant => (Decreases => Maps.Length (M), Decreases => 0),
     Pre                => Has_Key (M, K),
     Post               =>
       Cardinality_Rec (M) =
         Cardinality_Rec (Remove (M, K)) + Get (M, K);

   pragma Warnings (Off, "unused variable ""E""");
   procedure Lemma_Empty (M : Multiset) with
   --  This lemma eases the proof of Is_Empty bridging the gap between the
   --  Is_Empty function on functional maps and the one on multisets.

     Ghost,
     Pre  => Invariant (M.Map, M.Card),
     Post => Is_Empty (M.Map) = (for all E of M => False);
   pragma Warnings (On, "unused variable ""E""");

   procedure Lemma_Contains_Cardinality
     (Container : Multiset;
      Element   : Element_Type) with
   --  States that the cardinality of a multiset is larger than the number of
   --  occurences of each of its elements.

     Global => null,
     Pre    => Invariant (Container.Map, Container.Card)
       and then Contains (Container, Element),
     Post   => Nb_Occurence (Container, Element) <= Cardinality (Container);

   procedure Lemma_Leq_Cardinality (Left, Right : Maps.Map) with
   --  States that if Left contains less occurences of each element value than
   --  Right, then the cardinality of Left is smaller than the cardinality of
   --  Right.

     Ghost,
     Subprogram_Variant => (Decreases => Length (Left)),
     Pre                => (for all E of Left =>
                              Has_Key (Right, E)
                              and then Get (Left, E) <= Get (Right, E)),
     Post               => Cardinality_Rec (Left) <= Cardinality_Rec (Right);

   procedure Lemma_Equal_Except
     (Left : Multiset;
      Right : Multiset;
      Element : Element_Type) with
   --  This Lemma eases the proof of Equal_Except

     Ghost,
     Pre  =>
       (Invariant (Left.Map, Left.Card)
          and then Invariant (Right.Map, Right.Card)
          and then (for all E of Left =>
                      (if not Equivalent_Elements (E, Element)
                       then Nb_Occurence (Right, E) =
                              Nb_Occurence (Left, E)))),
     Post => Elements_Equal_Except (Left.Map, Right.Map, Element);

   procedure Lemma_Remove_Intersection
     (Left    : Multiset;
      Right   : Multiset;
      Element : Element_Type) with
   --  Expresses the behaviour of cardinality when removing an element from an
   --  intersection.

     Ghost,
     Global => null,
     Pre    => Invariant (Left.Map, Left.Card)
                 and then Invariant (Right.Map, Right.Card)
                 and then (Contains (Left, Element)
                             or else Contains (Right, Element)),
     Post   =>
       (if Contains (Left, Element)
        then (if Contains (Right, Element)
              then Cardinality (Intersection (Left, Right)) =
                     Cardinality (Intersection (Remove_All (Left, Element),
                                                Remove_All (Right, Element))) +
                       Min (Nb_Occurence (Left, Element),
                            Nb_Occurence (Right, Element))
               else Cardinality (Intersection (Left, Right)) =
                      Cardinality (Intersection (Remove_All (Left, Element),
                                                 Right)))
         else (if Contains (Right, Element)
               then Cardinality (Intersection (Left, Right)) =
                      Cardinality
                        (Intersection (Left, Remove_All (Right, Element)))));

   procedure Lemma_Remove_Union
     (Left    : Multiset;
      Right   : Multiset;
      Element : Element_Type) with
   --  Expresses the behaviour of the cardinality when removing an element from
   --  an Union.

     Ghost,
     Global => null,
     Pre    => Invariant (Left.Map, Left.Card)
                 and then Invariant (Right.Map, Right.Card)
                 and then (Contains (Left, Element)
                             or else Contains (Right, Element)),
     Post   =>
       (if Contains (Left, Element)
        then (if Contains (Right, Element)
              then Cardinality (Union (Left, Right)) =
                Cardinality
                  (Union
                    (Remove_All (Left, Element), Remove_All (Right, Element)))
                       + Max (Nb_Occurence (Left, Element),
                              Nb_Occurence (Right, Element))
              else Cardinality (Union (Left, Right)) =
                     Cardinality
                       (Union (Remove_All (Left, Element), Right))
                          + Nb_Occurence (Left, Element))
        else Cardinality (Union (Left, Right)) =
               Cardinality
                 (Union (Left, Remove_All (Right, Element)))
                    + Nb_Occurence (Right, Element));

   procedure Lemma_Sym_Intersection_Rec
     (Left  : Multiset;
      Right : Multiset)
   --  Recursive variant of the Lemma_Sym_Intersection lemma used to avoid
   --  polluting its visible specification with a variant.

   with
     Global => null,
     Pre    => Invariant (Left.Map, Left.Card)
       and then Invariant (Right.Map, Right.Card),
     Post   => Intersection (Left, Right) = Intersection (Right, Left),
     Subprogram_Variant => (Decreases => Cardinality (Left));

   procedure Lemma_Sym_Union_Rec
     (Left  : Multiset;
      Right : Multiset)
   --  Recursive variant of the Lemma_Sym_Union lemma used to avoid
   --  polluting its visible specification with a variant.

   with
     Global => null,
     Pre    => Invariant (Left.Map, Left.Card)
       and then Invariant (Right.Map, Right.Card),
     Post   => Union (Left, Right) = Union (Right, Left),
     Subprogram_Variant => (Decreases => Cardinality (Left));

   ----------
   -- "<=" --
   ----------

   function "<=" (Left : Multiset; Right : Multiset) return Boolean is
      Element : Element_Type;
      Buffer  : Multiset := Left;

   begin
      while not Is_Empty (Buffer) loop
         Element := Choose (Buffer);

         if Nb_Occurence (Left, Element) > Nb_Occurence (Right, Element) then
            return False;
         end if;

         Buffer := Remove_All (Buffer, Element);

         pragma Loop_Invariant
           (for all E of Left =>
              (if not Contains (Buffer, E)
               then Nb_Occurence (Left, E) <= Nb_Occurence (Right, E)
                      and then Has_Key (Right.Map, E)));
         pragma Loop_Invariant (Invariant (Buffer.Map, Buffer.Card));
         pragma Loop_Variant (Decreases => Cardinality (Buffer));
      end loop;

      Lemma_Leq_Cardinality (Left.Map, Right.Map);
      return True;
   end "<=";

   ---------
   -- "=" --
   ---------

   function "=" (Left, Right : Multiset) return Boolean is
   begin
      declare
         Buffer : Multiset := Left;
         E      : Element_Type;

      begin
         while not Is_Empty (Buffer) loop
            E := Choose (Buffer);

            if Nb_Occurence (Right, E) /= Nb_Occurence (Left, E) then
               return False;
            end if;

            Buffer := Remove_All (Buffer, E);

            pragma Loop_Invariant (Invariant (Buffer.Map, Buffer.Card));
            pragma Loop_Invariant (Buffer <= Left);
            pragma Loop_Invariant
              (for all Element of Left =>
                 (if not Contains (Buffer, Element)
                  then Maps.Has_Key (Right.Map, Element)));
            pragma Loop_Invariant
              (for all Element of Left =>
                 (if not Contains (Buffer, Element)
                  then Maps.Get (Right.Map, Element) =
                         Maps.Get (Left.Map, Element)));

            pragma Loop_Variant (Decreases => Cardinality (Buffer));
         end loop;

         Lemma_Leq_Cardinality (Left.Map, Right.Map);

         Buffer := Right;
         while not Is_Empty (Buffer) loop
            E := Choose (Buffer);

            if Nb_Occurence (Right, E) /= Nb_Occurence (Left, E) then
               return False;
            end if;

            Buffer := Remove_All (Buffer, E);
            pragma Loop_Invariant (Invariant (Buffer.Map, Buffer.Card));
            pragma Loop_Invariant (Buffer <= Right);
            pragma Loop_Invariant
              (for all Element of Right =>
                 (if not Contains (Buffer, Element)
                  then Maps.Has_Key (Left.Map, Element)));
            pragma Loop_Invariant
              (for all Element of Right =>
                 (if not Contains (Buffer, Element)
                  then Maps.Get (Right.Map, Element) =
                         Maps.Get (Left.Map, Element)));

            pragma Loop_Variant (Decreases => Cardinality (Buffer));
         end loop;

         Lemma_Leq_Cardinality (Right.Map, Left.Map);

         return True;
      end;
   end "=";

   ---------
   -- Add --
   ---------

   function Add
     (Container : Multiset;
      Element   : Element_Type;
      Count     : Big_Positive) return Multiset is
   begin
      return M : Multiset do
         if Count > 0 then
            if Has_Key (Container.Map, Element) then
               M.Map := Set (Container.Map,
                             Element,
                             Get (Container.Map, Element) + Count);
               Lemma_Eq (Remove (M.Map, Element),
                         Remove (Container.Map, Element));
               Lemma_Remove (Container.Map, Element);
            else
               M.Map := Add (Container.Map, Element, Count);
               Lemma_Eq (Remove (M.Map, Element), Container.Map);
            end if;
            M.Card := Container.Card + Count;
            Lemma_Remove (M.Map, Element);
         end if;
      end return;
   end Add;

   function Add
     (Container : Multiset;
      Element   : Element_Type) return Multiset is
   begin
      return Add (Container, Element, 1);
   end Add;

   -----------------
   -- Cardinality --
   -----------------

   function Cardinality (Container : Multiset) return Big_Natural is
     (Container.Card);

   ---------------------
   -- Cardinality_Rec --
   ---------------------

   function Cardinality_Rec (Container : Maps.Map) return Big_Natural is
    (if Length (Container) = 0 then 0
     else Get (Container, Choose (Container))
            + Cardinality_Rec (Remove (Container, Choose (Container))));

   --------------
   -- Contains --
   --------------

   function Contains
     (Container : Multiset;
      Element   : Element_Type) return Boolean is
   begin
      return Has_Key (Container.Map, Element);
   end Contains;

   ------------
   -- Choose --
   ------------

   function Choose (Container : Multiset) return Element_Type is
      (Choose (Container.Map));

   ----------------
   -- Difference --
   ----------------

   function Difference
     (Left  : Multiset;
      Right : Multiset) return Multiset is
      Set     : Multiset;
      Count   : Big_Integer;
      Buffer  : Multiset := Left;
      Element : Element_Type;

   begin

      while not Is_Empty (Buffer) loop
         Element := Choose (Buffer);
         Buffer  := Remove_All (Buffer, Element);

         Count := Nb_Occurence (Left, Element) - Nb_Occurence (Right, Element);
         if Count > 0 then
            Set := Add (Set, Element, Count);
         end if;

         pragma Loop_Variant (Decreases => Cardinality (Buffer));

         pragma Loop_Invariant (Invariant (Buffer.Map, Buffer.Card));
         pragma Loop_Invariant (Invariant (Set.Map, Set.Card));
         pragma Loop_Invariant
           (for all E of Buffer => Nb_Occurence (Set, E) = 0);
         pragma Loop_Invariant
           (for all E of Set =>
              Nb_Occurence (Set, E) =
                Nb_Occurence (Left, E) - Nb_Occurence (Right, E));
         pragma Loop_Invariant
           (for all E of Left =>
              (if not Contains (Buffer, E)
                    and then Nb_Occurence (Left, E)
                               - Nb_Occurence (Right, E) > 0
               then Contains (Set, E)));

      end loop;
      return Set;
   end Difference;

   --------------------
   -- Empty_Multiset --
   --------------------

   function Empty_Multiset return Multiset is
   begin
      return (others => <>);
   end Empty_Multiset;

   ------------------
   -- Equal_Except --
   ------------------

   function Equal_Except
     (Left    : Multiset;
      Right   : Multiset;
      Element : Element_Type) return Boolean is

   begin
      return B : Boolean :=
        Elements_Equal_Except (Left.Map, Right.Map, Element)
          and then Elements_Equal_Except (Right.Map, Left.Map, Element)
      do
         if (for all E of Left =>
          (if not Equivalent_Elements (E, Element)
           then Nb_Occurence (Left, E) = Nb_Occurence (Right, E)))
         then
            Lemma_Equal_Except (Left, Right, Element);
         end if;

         if (for all E of Right =>
               (if not Equivalent_Elements (E, Element)
                then Nb_Occurence (Left, E) = Nb_Occurence (Right, E)))
         then
            Lemma_Equal_Except (Right, Left, Element);
         end if;
      end return;
   end Equal_Except;

   ------------------
   -- Intersection --
   ------------------

   function Intersection
     (Left  : Multiset;
      Right : Multiset) return Multiset
   is
      Set    : Multiset;
      Buffer : Multiset := Left;
      E      : Element_Type;
      Occ    : Big_Integer;

   begin
      while not Is_Empty (Buffer) loop
         E := Choose (Buffer);
         Buffer := Remove_All (Buffer, E);

         Occ := Min (Nb_Occurence (Left, E), Nb_Occurence (Right, E));
         if Occ > 0 then
            Set := Add (Set, E, Occ);
         end if;

         pragma Assert
           (for all Element of Set =>
              Nb_Occurence (Set, Element) <= Nb_Occurence (Left, Element));
         pragma Assert (for all Element of Set => Contains (Left, Element));
         pragma Assert (for all Element of Set => Has_Key (Left.Map, Element));
         pragma Assert
           (for all Element of Set =>
              Has_Key (Left.Map, Element)
                and then Get (Set.Map, Element) <= Get (Left.Map, Element));
         Lemma_Leq_Cardinality (Set.Map, Left.Map);
         pragma Assert (Cardinality (Set) <= Cardinality (Left));

         pragma Assert
           (for all Element of Set =>
              Has_Key (Right.Map, Element)
                and then Get (Set.Map, Element) <= Get (Right.Map, Element));
         Lemma_Leq_Cardinality (Set.Map, Right.Map);

         pragma Loop_Variant (Decreases => Cardinality (Buffer));

         pragma Loop_Invariant (Invariant (Buffer.Map, Buffer.Card));
         pragma Loop_Invariant (Invariant (Set.Map, Set.Card));
         pragma Loop_Invariant (Set <= Left);
         pragma Loop_Invariant (Set <= Right);
         pragma Loop_Invariant
           (for all Element of Buffer => Nb_Occurence (Set, Element) = 0);

         pragma Loop_Invariant
           (for all Element of Left =>
              (if not Contains (Buffer, Element)
               then Min (Nb_Occurence (Left, Element),
                         Nb_Occurence (Right, Element)) =
                      Nb_Occurence (Set, Element)));

      end loop;
      return Set;
   end Intersection;

   ---------------
   -- Invariant --
   ---------------

   function Invariant (Container : Map; Card : Big_Natural) return Boolean is
      (Card = Cardinality_Rec (Container));

   --------------
   -- Is_Empty --
   --------------

   function Is_Empty (Container : Multiset) return Boolean is
      B : Boolean := Is_Empty (Container.Map);

   begin
      Lemma_Empty (Container);
      return B;
   end Is_Empty;

   --------------------------------
   -- Lemma_Contains_Cardinality --
   --------------------------------

   procedure Lemma_Contains_Cardinality
     (Container : Multiset;
      Element   : Element_Type) is
   begin
      Lemma_Remove (Container.Map, Element);
   end Lemma_Contains_Cardinality;

   -----------------
   -- Lemma_Empty --
   -----------------

   procedure Lemma_Empty (M : Multiset) is
   begin
      if not Is_Empty (M.Map) then
         declare
            Element : constant Element_Type := Choose (M.Map);
         begin
            pragma Assert (Contains (M, Element));
         end;
      end if;
   end Lemma_Empty;

   --------------
   -- Lemma_Eq --
   --------------

   procedure Lemma_Eq (M1, M2 : Maps.Map) is
   begin
      if Length (M1) /= 0 then
         declare
            E : constant Element_Type := Choose (M2);
         begin
            Lemma_Remove (M1, E);
            Lemma_Eq (Remove (M1, E), Remove (M2, E));
         end;
      end if;
   end Lemma_Eq;

   ------------------------
   -- Lemma_Equal_Except --
   ------------------------

   procedure Lemma_Equal_Except
     (Left  : Multiset;
      Right : Multiset; Element : Element_Type)
   is
      Buffer : Map := Left.Map;
      E      : Element_Type;
   begin
      while not Is_Empty (Buffer) loop
         E := Choose (Buffer);

         if not Equivalent_Elements (E, Element) then
            pragma Assert (Nb_Occurence (Right, E) /= 0);
            pragma Assert (Has_Key (Right.Map, E));
            pragma Assert (Get (Left.Map, E) = Get (Right.Map, E));
         end if;

         Buffer := Remove (Buffer, E);

         pragma Loop_Variant (Decreases => Length (Buffer));
         pragma Loop_Invariant (Buffer <= Left.Map);
         pragma Loop_Invariant
           (for all El of Left =>
              (if not Has_Key (Buffer, El)
                    and then not Equivalent_Elements (El, Element)
               then Has_Key (Right.Map, El)
                      and then Get (Left.Map, El) = Get (Right.Map, El)));
      end loop;
   end Lemma_Equal_Except;

   ---------------------------
   -- Lemma_Leq_Cardinality --
   ---------------------------

   procedure Lemma_Leq_Cardinality (Left, Right : Maps.Map) is
      E : Element_Type;
   begin
      if not Is_Empty (Left) then
         E := Choose (Left);

         Lemma_Remove (Left, E);

         Lemma_Remove (Right, E);
         Lemma_Leq_Cardinality (Remove (Left, E), Remove (Right, E));
      end if;
   end Lemma_Leq_Cardinality;

   -----------------------------------
   -- Lemma_Nb_Occurence_Equivalent --
   -----------------------------------

   procedure Lemma_Nb_Occurence_Equivalent
     (Container            : Multiset;
      Element_1, Element_2 : Element_Type)
   is
   begin
      if not Has_Key (Container.Map, Element_1) then
         Lemma_Has_Key_Equivalent (Container.Map, Element_1);
         pragma Assert (Nb_Occurence (Container, Element_1) =
                          Nb_Occurence (Container, Element_2));
      elsif not Has_Key (Container.Map, Element_2) then
         Lemma_Has_Key_Equivalent (Container.Map, Element_2);
         pragma Assert (Nb_Occurence (Container, Element_1) =
                          Nb_Occurence (Container, Element_2));
      else
         Lemma_Get_Equivalent (Container.Map, Element_1, Element_2);
         pragma Assert (Nb_Occurence (Container, Element_1) =
                          Nb_Occurence (Container, Element_2));
      end if;
   end Lemma_Nb_Occurence_Equivalent;

   ------------------
   -- Lemma_Remove --
   ------------------

   procedure Lemma_Remove (M : Maps.Map; K : Element_Type) is
      L : constant Element_Type := Choose (M);
   begin
      if not Equivalent_Elements (L, K) then
         Lemma_Remove (Remove (M, L), K);
         Lemma_Eq (Remove (Remove (M, L), K), Remove (Remove (M, K), L));
         Lemma_Remove (Remove (M, K), L);
      else
         Lemma_Eq (Remove (M, L), Remove (M, K));
      end if;
   end Lemma_Remove;

   -------------------------------
   -- Lemma_Remove_Intersection --
   -------------------------------

   procedure Lemma_Remove_Intersection
     (Left    : Multiset;
      Right   : Multiset;
      Element : Element_Type)
     is
      Int  : constant Multiset := Intersection (Left, Right);
      RInt : Multiset;
      IntR : Multiset;

   begin
      if Contains (Left, Element) and then Contains (Right, Element) then
         RInt := Remove_All (Int, Element);
         IntR :=
           Intersection
             (Remove_All (Left, Element), Remove_All (Right, Element));

         pragma Assert (for all E of IntR => Contains (Int, E));
         pragma Assert
           (for all E of IntR =>
              Nb_Occurence (Int, E) = Nb_Occurence (IntR, E));
         pragma Assert
           (for all E of Int =>
              (if not Equivalent_Elements (E, Element)
               then Contains (IntR, E)));

         --  RInt <= IntR
         pragma Assert
           (for all E of RInt =>
              Nb_Occurence (RInt, E) = Nb_Occurence (IntR, E));
         pragma Assert (for all E of RInt => Contains (IntR, E));
         pragma Assert (for all E of RInt => Nb_Occurence (IntR, E) /= 0);
         pragma Assert (for all E of RInt => Has_Key (IntR.Map, E));
         Lemma_Leq_Cardinality (RInt.Map, IntR.Map);
         pragma Assert (RInt <= IntR);

         --  IntR <= RInt
         pragma Assert (for all E of IntR => Nb_Occurence (RInt, E) /= 0);

         pragma Assert
           (for all E of IntR =>
              Nb_Occurence (IntR, E) = Nb_Occurence (RInt, E));
         pragma Assert (for all E of IntR => Has_Key (RInt.Map, E));
         Lemma_Leq_Cardinality (IntR.Map, RInt.Map);

         pragma Assert (IntR <= RInt);

         pragma Assert (Cardinality (RInt) = Cardinality (IntR));
      else
         if Contains (Left, Element) then
            IntR := Intersection (Remove_All (Left, Element), Right);
         else
            IntR := Intersection (Left, Remove_All (Right, Element));
         end if;

         --  IntR <= Int
         pragma Assert
           (for all E of IntR =>
              Nb_Occurence (IntR, E) = Nb_Occurence (Int, E)
                and then Has_Key (Int.Map, E));
         Lemma_Leq_Cardinality (IntR.Map, Int.Map);

         pragma Assert (IntR <= Int);

         --  Int <= IntR
         pragma Assert
           (for all E of Int =>
              Nb_Occurence (Int, E) = Nb_Occurence (IntR, E)
                and then Has_Key (IntR.Map, E));
         Lemma_Leq_Cardinality (Int.Map, IntR.Map);

         pragma Assert (Int <= IntR);

      end if;

   end Lemma_Remove_Intersection;

   ------------------------
   -- Lemma_Remove_Union --
   ------------------------

   procedure Lemma_Remove_Union
     (Left    : Multiset;
      Right   : Multiset;
      Element : Element_Type)
   is
      U       : constant Multiset := Union (Left, Right);
      R_Union : constant Multiset := Remove_All (U, Element);
      Union_R : Multiset;

   begin
      if Contains (Left, Element) and then Contains (Right, Element) then
         Union_R :=
           Union (Remove_All (Left, Element), Remove_All (Right, Element));

         --  R_Union <= Union_R
         pragma Assert
           (for all E of R_Union =>
              Get (R_Union.Map, E) = Get (Union_R.Map, E)
                and then  Has_Key (Union_R.Map, E));
         Lemma_Leq_Cardinality (R_Union.Map, Union_R.Map);

         pragma Assert (R_Union <= Union_R);

         --  Union_R <= R_Union
         pragma Assert
           (for all E of Union_R => Has_Key (R_Union.Map, E));
         Lemma_Leq_Cardinality (Union_R.Map, R_Union.Map);

         pragma Assert (Union_R <= R_Union);

         pragma Assert (Cardinality (Union_R) = Cardinality (R_Union));

         Lemma_Remove (U.Map, Element);
      else
         if Contains (Left, Element) then
            Union_R := Union (Remove_All (Left, Element), Right);
         else
            Union_R := Union (Left, Remove_All (Right, Element));
         end if;

         --  R_Union <= Union_R
         pragma Assert
           (for all E of R_Union =>
              Get (R_Union.Map, E) = Get (Union_R.Map, E)
                and then  Has_Key (Union_R.Map, E));
         Lemma_Leq_Cardinality (R_Union.Map, Union_R.Map);

         pragma Assert (R_Union <= Union_R);

         --  Union_R <= R_Union
         pragma Assert
           (for all E of Union_R => Has_Key (R_Union.Map, E));
         Lemma_Leq_Cardinality (Union_R.Map, R_Union.Map);

         pragma Assert (Union_R <= R_Union);

         pragma Assert (Cardinality (Union_R) = Cardinality (R_Union));

         Lemma_Remove (U.Map, Element);
      end if;
   end Lemma_Remove_Union;

   ----------------------------
   -- Lemma_Sym_Intersection --
   ----------------------------

   procedure Lemma_Sym_Intersection
     (Left  : Multiset;
      Right : Multiset)
   renames Lemma_Sym_Intersection_Rec;

   --------------------------------
   -- Lemma_Sym_Intersection_Rec --
   --------------------------------

   procedure Lemma_Sym_Intersection_Rec
     (Left  : Multiset;
      Right : Multiset)
   is
      E : Element_Type;
   begin
      if not Is_Empty (Left) then
         E := Choose (Left);
         Lemma_Remove_Intersection (Left, Right, E);
         Lemma_Remove_Intersection (Right, Left, E);
         if Contains (Right, E) then
            Lemma_Sym_Intersection_Rec
              (Remove_All (Left, E), Remove_All (Right, E));

            pragma Assert
              (Cardinality (Intersection (Left, Right)) =
                 Cardinality (Intersection (Right, Left)));
         else
            Lemma_Sym_Intersection_Rec (Remove_All (Left, E), Right);
         end if;
      end if;
   end Lemma_Sym_Intersection_Rec;

   -------------------
   -- Lemma_Sym_Sum --
   -------------------

   procedure Lemma_Sym_Sum
     (Left  : Multiset;
      Right : Multiset) is
   begin
      null;
   end Lemma_Sym_Sum;

   ---------------------
   -- Lemma_Sym_Union --
   ---------------------

   procedure Lemma_Sym_Union
     (Left  : Multiset;
      Right : Multiset)
   renames Lemma_Sym_Union_Rec;

   -------------------------
   -- Lemma_Sym_Union_Rec --
   -------------------------

   procedure Lemma_Sym_Union_Rec
     (Left  : Multiset;
      Right : Multiset)
   is
      E : Element_Type;
   begin
      if not Is_Empty (Left) then
         E := Choose (Left);

         Lemma_Remove_Union (Left, Right, E);
         Lemma_Remove_Union (Right, Left, E);

         if Contains (Right, E) then
            Lemma_Sym_Union_Rec (Remove_All (Left, E), Remove_All (Right, E));

            pragma Assert (Union (Left, Right) = Union (Right, Left));
         else
            Lemma_Sym_Union_Rec (Remove_All (Left, E), Right);

            pragma Assert (Union (Left, Right) = Union (Right, Left));
         end if;
      else
         pragma Assert (Union (Left, Right) = Union (Right, Left));
      end if;

      pragma Assert (Union (Left, Right) = Union (Right, Left));
   end Lemma_Sym_Union_Rec;

   ------------------
   -- Nb_Occurence --
   ------------------

   function Nb_Occurence
     (Container : Multiset;
      Element   : Element_Type) return Big_Natural
   is (if Has_Key (Container.Map, Element)
       then Get (Container.Map, Element)
       else 0);

   ----------
   -- Next --
   ----------

   function Next
     (Iterator : Iterable_Multiset; Cursor : Multiset) return Multiset
   is
      R : constant Multiset := Remove_All (Cursor, Choose (Cursor));
      C : constant Map := Next (Iterator.Map, Cursor.Map) with Ghost;
   begin
      return R;
   end Next;

   ------------
   -- Remove --
   ------------

   function Remove
     (Container : Multiset;
      Element   : Element_Type;
      Count     : Big_Positive := 1) return Multiset is
   begin
      if Count = Nb_Occurence (Container, Element) then
         return Remove_All (Container, Element);
      else
         declare
            Result : Multiset;

         begin
            Result.Map :=
              Set (Container.Map,
                   Element, Nb_Occurence (Container, Element) - Count);
            Lemma_Contains_Cardinality (Container, Element);
            Result.Card := Cardinality (Container) - Count;

            Lemma_Remove (Result.Map, Element);
            Lemma_Remove (Container.Map, Element);

            Lemma_Eq
              (Remove (Result.Map, Element), Remove (Container.Map, Element));

            return Result;
         end;
      end if;


   end Remove;

   ----------------
   -- Remove_All --
   ----------------

   function Remove_All
     (Container : Multiset;
      Element   : Element_Type) return Multiset
   with Refined_Post =>
     Invariant (Remove_All'Result.Map, Remove_All'Result.Card)
     and then not Contains (Remove_All'Result, Element)
     and then Cardinality (Remove_All'Result) =
       Cardinality (Container) - Nb_Occurence (Container, Element)
     and then Equal_Except (Container, Remove_All'Result, Element)
     and then Map_Logic_Equal
       (Remove_All'Result.Map, Remove (Container.Map, Element))
   is
   begin
      return Set : Multiset do
         Set.Map  := Remove (Container.Map, Element);
         Lemma_Remove (Container.Map, Element);
         Set.Card := Container.Card - Get (Container.Map, Element);
      end return;
   end Remove_All;

   -----------
   -- Union --
   -----------

   function Sum (Left : Multiset; Right : Multiset) return Multiset is
      E         : Element_Type;
      Set_Union : Multiset := Left;
      Buffer    : Multiset;


   begin
      Buffer := Right;
      while not Is_Empty (Buffer) loop
         E := Choose (Buffer);

         Set_Union := Add (Set_Union, E, Get (Buffer.Map, E));
         Buffer := Remove_All (Buffer, E);

         pragma Loop_Variant (Decreases => Cardinality (Buffer));
         pragma Loop_Invariant (Invariant (Set_Union.Map, Set_Union.Card));
         pragma Loop_Invariant (Invariant (Buffer.Map, Buffer.Card));
         pragma Loop_Invariant
           (Cardinality (Set_Union) + Cardinality (Buffer) =
                Cardinality (Left) + Cardinality (Right));
         pragma Loop_Invariant
           (for all Element of Right =>
              Contains (Set_Union, Element)
                or else Contains (Buffer, Element));
         pragma Loop_Invariant
           (for all Element of Left => Contains (Set_Union, Element));
         pragma Loop_Invariant
           (for all Element of Buffer =>
              Nb_Occurence (Set_Union, Element) =
                Nb_Occurence (Left, Element));
         pragma Loop_Invariant
           (for all Element of Buffer =>
              Nb_Occurence (Buffer, Element) =
                Nb_Occurence (Right, Element));
         pragma Loop_Invariant
           (for all Element of Set_Union =>
              (if Contains (Buffer, Element)
               then Nb_Occurence (Set_Union, Element) =
                      Nb_Occurence (Left, Element)
               else Nb_Occurence (Set_Union, Element) =
                      Nb_Occurence (Left, Element) +
                        Nb_Occurence (Right, Element)));
      end loop;

      return Set_Union;
   end Sum;

   -----------
   -- Union --
   -----------

   function Union
     (Left  : Multiset;
      Right : Multiset) return Multiset
   is
      Set    : Multiset := Left;
      Buffer : Multiset := Right;
      E      : Element_Type;
      Occ    : Big_Integer;

   begin
      while not Is_Empty (Buffer) loop
         E := Choose (Buffer);
         Buffer := Remove_All (Buffer, E);

         Occ := Max (Nb_Occurence (Left, E), Nb_Occurence (Right, E));
         if Occ > Nb_Occurence (Set, E) then
            Set :=
              Add (Set, E, Occ - Nb_Occurence (Set, E));
         end if;

         pragma Loop_Variant (Decreases => Cardinality (Buffer));

         pragma Loop_Invariant (Invariant (Buffer.Map, Buffer.Card));
         pragma Loop_Invariant (Invariant (Set.Map, Set.Card));
         pragma Loop_Invariant
           (for all Element of Buffer =>
              Nb_Occurence (Set, Element) = Nb_Occurence (Left, Element));

         pragma Loop_Invariant (Left <= Set);
         pragma Loop_Invariant
           (for all Element of Right =>
             (if not Contains (Buffer, Element)
              then Has_Key (Set.Map, Element)));
         pragma Loop_Invariant
           (for all Element of Set =>
              (if not Contains (Buffer, Element)
               then Nb_Occurence (Set, Element) =
                      Max (Nb_Occurence (Left, Element),
                           Nb_Occurence (Right, Element))));

      end loop;
      Lemma_Leq_Cardinality (Right.Map, Set.Map);
      return Set;
   end Union;

end SPARK.Containers.Functional.Multisets;
