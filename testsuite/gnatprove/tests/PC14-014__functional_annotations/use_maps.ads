pragma Ada_2012;
with Ada.Containers.Formal_Hashed_Maps;
with Ada.Containers; use Ada.Containers;

package Use_Maps with SPARK_Mode is

   function Hash (Id : Natural) return Hash_Type is (Hash_Type (Id));

   package My_Maps is new Ada.Containers.Formal_Hashed_Maps
     (Element_Type    => Integer,
      Key_Type        => Positive,
      Hash            => Hash,
      Equivalent_Keys => "=");

   use My_Maps;
   use My_Maps.Formal_Model;

   pragma Unevaluated_Use_Of_Old (Allow);

   function My_Find (S : My_Maps.Map; K : Positive) return Cursor
     with
       Post => (if My_Find'Result /= No_Element
                then Has_Element (S, My_Find'Result)
                  and then Key (S, My_Find'Result) = K
                else not Contains (Model (S), K));
   --  Iterate through the set to find K.

   function My_Contains (S : My_Maps.Map; K : Positive) return Boolean
     is (Contains (S, K)) with
   Post => (if My_Contains'Result then My_Find (S, K) /= No_Element
            else My_Find (S, K) = No_Element);

   function F (E : Integer) return Integer is
      (if E in -100 .. 100 then E * 2 else E);

   procedure Apply_F (S : My_Maps.Map; R : in out My_Maps.Map) with
     Pre  => Length (S) <= R.Capacity,
     Post => Length (R) = Length (S)
     and (for all K of S =>
              (for some L of R => Element (R, L) = F (Element (S, K))))
     and (for all L of R =>
              (for some K of S => Element (R, L) = F (Element (S, K))));
   --  Store in R the image of every element of S through F.

   procedure Apply_F_2 (S : My_Maps.Map; R : in out My_Maps.Map) with
     Pre  => Length (S) <= R.Capacity,
     Post => Length (R) = Length (S)
     and (for all K of R => Contains (Model (S), K))
     and (for all K of S => Contains (Model (R), K)
          and then Element (R, K)  = F (Element (S, K)));
   --  Same as before except that we also want Keys to be preserved.

   procedure Apply_F_3 (S : in out My_Maps.Map) with
     Post => Length (S) = Length (S)'Old
     and (for all K of Keys (S)'Old =>
              (for some L of S =>
                     Element (S, L) = F (Element (Model (S)'Old, K))))
     and (for all L of S =>
              (for some K of Keys (S)'Old =>
                     Element (S, L) = F (Element (Model (S)'Old, K))));
   --  Replace every element of S by its image through F.

   procedure Apply_F_4 (S : in out My_Maps.Map) with
     Post => Length (S) = Length (S)'Old
     and Keys (S) = Keys (S)'Old
     and (for all K of S =>
              Element (S, K)  = F (Element (Model (S)'Old, K)));
   --  Same as before except that we also want Keys to be preserved.

   function Are_Disjoint (S1, S2 : My_Maps.Map) return Boolean with
     Post => Are_Disjoint'Result =
       (for all E of S2 => not Contains (Model (S1), E));
   --  Check wether two maps have a disjoint set of Keys.

   function Prop (E : Integer) return Boolean is
     (E >= 0);

   procedure Union_Prop (S1 : in out My_Maps.Map; S2 : My_Maps.Map) with
     Pre  => (for all K of S1 => Prop (Element (S1, K)))
     and (for all K of S2 => Prop (Element (S2, K)))
     and S1.Capacity - Length (S1) > Length (S2),
     Post => (for all K of S1 => Prop (Element (S1, K)));
   --  Compute the union of two maps for which Prop is true.

   Count : constant := 5;

   procedure Insert_Count (M : in out My_Maps.Map)
   --  Insert 0 Count times at Keys 1 .. Count.

   with
     Pre  => M.Capacity - Count > Length (M)
     and (for all K of M => K > Count),
     Post => Length (M) <= Length (M)'Old + Count
     and (for all K of M =>
            (if K > Count then Contains (Model (M)'Old, K)
             and then Element (M, K) = Element (Model (M)'Old, K)))
     and (for all K in 1 .. Count => Contains (Model (M), K)
          and then Element (M, K) = 0);

   --  Test links between high-level Model, lower-level position based Model
   --  and lowest-level, cursor based Model of a map.

   function Q (E : Integer) return Boolean;
   --  Any property Q on an Integer E.

   procedure From_Keys_To_Model (S : My_Maps.Map) with
     Ghost,
     Global => null,
     Pre    => (for all I in 1 .. Length (S) =>
                    Q (Element (S, K.Get (Keys (S), I)))),
     Post   => (for all K of S => Q (Element (S, K)));
   --  Test that the link can be done from a property on the elements of a
   --  low level, position based view of a container and its high level view.

   procedure From_Model_To_Keys (S : My_Maps.Map) with
     Ghost,
     Global => null,
     Pre    => (for all K of Model (S) => Q (Element (S, K))),
     Post   => (for all I in 1 .. Length (S) =>
                    Q (Element (S, K.Get (Keys (S), I))));
   --  Test that the link can be done from a property on the elements of a
   --  high level view of a container and its lower level, position based view.

   procedure From_Keys_To_Cursors (S : My_Maps.Map) with
     Ghost,
     Global => null,
     Pre    => (for all I in 1 .. Length (S) =>
                    Q (Element (S, K.Get (Keys (S), I)))),
     Post   => (for all Cu in S => Q (Element (S, Cu)));
   --  Test that the link can be done from a property on the elements of a
   --  position based view of a container and its lowest level, cursor aware
   --  view.

   procedure From_Cursors_To_Keys (S : My_Maps.Map) with
     Ghost,
     Global => null,
     Pre    => (for all Cu in S => Q (Element (S, Cu))),
     Post   => (for all I in 1 .. Length (S) =>
                    Q (Element (S, K.Get (Keys (S), I))));
   --  Test that the link can be done from a property on the elements of a
   --  cursor aware view of a container and its position based view.

   procedure From_Model_To_Cursors (S : My_Maps.Map) with
     Ghost,
     Global => null,
     Pre    => (for all K of Model (S) => Q (Element (S, K))),
     Post   => (for all Cu in S => Q (Element (S, Cu)));
   --  Test that the link can be done from a property on the elements of a
   --  high level view of a container and its lowest level, cursor aware view.

   procedure From_Cursors_To_Model (S : My_Maps.Map) with
     Ghost,
     Global => null,
     Pre    => (for all Cu in S => Q (Element (S, Cu))),
     Post   => (for all K of S => Q (Element (S, K)));
   --  Test that the link can be done from a property on the elements of a
   --  low level, cursor aware view of a container and its high level view.
end Use_Maps;
