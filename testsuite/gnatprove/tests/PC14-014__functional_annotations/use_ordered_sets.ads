pragma Ada_2012;
with Ada.Containers;       use Ada.Containers;
with Ada.Containers.Formal_Ordered_Sets;

package Use_Ordered_Sets with SPARK_Mode is
   type Element_Type is new Integer;
   package My_Sets is new Ada.Containers.Formal_Ordered_Sets
     (Element_Type => Element_Type);
   use My_Sets;
   use My_Sets.Formal_Model;
   pragma Unevaluated_Use_Of_Old (Allow);

   function My_Contains (S : My_Sets.Set; E : Element_Type) return Boolean is
     (Find (S, E) /= No_Element) with
   Post => My_Contains'Result = Contains (S, E);

   function My_Find (S : My_Sets.Set; E : Element_Type) return Cursor with
     Post => My_Find'Result = Find (S, E);
   --  Iterate through the set to find E.

   function F (E : Element_Type) return Element_Type is
      (if E in -100 .. 100 then E * 2 else E);

   procedure Apply_F (S : My_Sets.Set; R : in out My_Sets.Set) with
     Pre  => R.Capacity >= Length (S),
     Post => (for all E of S => M.Contains (Model (R), F (E)))
     and (for all G of R =>
              (for some E of S => G = F (E)));
   --  Store in R the image of every element of S through F. Note that F is not
   --  injective.

   function Are_Disjoint (S1, S2 : My_Sets.Set) return Boolean with
     Post => Are_Disjoint'Result =
       M.Is_Empty (M.Intersection (Model (S1), Model (S2)));
   --  Check wether two sets are disjoint.

   function Are_Disjoint_2 (S1, S2 : My_Sets.Set) return Boolean with
     Post => Are_Disjoint_2'Result =
       (for all E of Model (S2) => not M.Contains (Model (S1), E));
   --  Same as before except that it is specified it using a quantified
   --  expression instead of set intersection.

   function Prop (E : Element_Type) return Boolean is
     (E >= 0);

   procedure Union_Prop (S1 : in out My_Sets.Set; S2 : My_Sets.Set) with
     Pre  => (for all E of S1 => Prop (E))
     and (for all E of S2 => Prop (E))
     and S1.Capacity - Length (S1) > Length (S2),
     Post => (for all E of S1 => Prop (E));
   --  Compute the union of two sets for which Prop is true.

   procedure Move (S1, S2 : in out My_Sets.Set) with
     Pre  => S2.Capacity >= Length (S1),
     Post => Model (S1)'Old = Model (S2) and Length (S1) = 0;
   --  Move the content of a set into another set. Already included element are
   --  excluded from the first set during iteration.

   procedure Move_2 (S1, S2 : in out My_Sets.Set) with
     Pre  => S2.Capacity >= Length (S1),
     Post => Model (S1)'Old = Model (S2) and Elements (S1)'Old = Elements (S2)
     and Length (S1) = 0;
   --  Same as before except that we want the order of elements to be
   --  preserved.

   procedure Move_3 (S1, S2 : in out My_Sets.Set) with
     Pre  => S2.Capacity >= Length (S1),
     Post => Model (S1)'Old = Model (S2) and Length (S1) = 0;
   --  Move the content of a set into another set. S1 is cleared at the end.

   procedure Move_4 (S1, S2 : in out My_Sets.Set) with
     Pre  => S2.Capacity >= Length (S1),
     Post => Model (S1)'Old = Model (S2) and Elements (S1)'Old = Elements (S2)
     and Length (S1) = 0;
   --  Same as before except that we want the order of elements to be
   --  preserved.

   procedure Double_Size (S : in out My_Sets.Set)
   --  Double the size of a set containing only even numbers by adding the
   --  successor of every element.

   with
     Pre  => S.Capacity / 2 >= Length (S) and
     (for all E of S => E mod 2 = 0),
     Post => Length (S) = 2 * Length (S)'Old
     and (for all I in 1 .. Length (S)'Old =>
       E.Get (Elements (S), 2 * I - 1) = E.Get (Elements (S)'Old, I)
       and E.Get (Elements (S), 2 * I) =
           E.Get (Elements (S)'Old, I) + 1);

   Count : constant := 5;

   procedure Insert_Count (S : in out My_Sets.Set)
   --  Include elements 1 .. Count in S.

   with
     Pre  => S.Capacity - Count > Length (S),
     Post => Length (S) <= Length (S)'Old + Count
     and Model (S)'Old <= Model (S)
     and (for all E in 1 .. Element_Type'(Count) => Contains (S, E))
     and (for all E of S => M.Contains (Model (S)'Old, E) or E in 1 .. Count);

   --  Test links between high-level model, lower-level position based model
   --  and lowest-level, cursor based model of a set.

   function Q (E : Element_Type) return Boolean;
   --  Any property Q on an Integer E.

   procedure From_Elements_To_Model (S : My_Sets.Set) with
     Ghost,
     Global => null,
     Pre    => (for all I in 1 .. Length (S) =>
                    Q (E.Get (Elements (S), I))),
     Post   => (for all E of Model (S) => Q (E));
   --  Test that the link can be done from a property on the elements of a
   --  low level, position based view of a container and its high level view.

   procedure From_Model_To_Elements (S : My_Sets.Set) with
     Ghost,
     Global => null,
     Pre    => (for all E of Model (S) => Q (E)),
     Post   => (for all I in 1 .. Length (S) =>
                    Q (E.Get (Elements (S), I)));
   --  Test that the link can be done from a property on the elements of a
   --  high level view of a container and its lower level, position based view.

   procedure From_Elements_To_Cursors (S : My_Sets.Set) with
     Ghost,
     Global => null,
     Pre    => (for all I in 1 .. Length (S) =>
                    Q (E.Get (Elements (S), I))),
     Post   => (for all Cu in S => Q (Element (S, Cu)));
   --  Test that the link can be done from a property on the elements of a
   --  position based view of a container and its lowest level, cursor aware
   --  view.

   procedure From_Cursors_To_Elements (S : My_Sets.Set) with
     Ghost,
     Global => null,
     Pre    => (for all Cu in S => Q (Element (S, Cu))),
     Post   => (for all I in 1 .. Length (S) =>
                    Q (E.Get (Elements (S), I)));
   --  Test that the link can be done from a property on the elements of a
   --  cursor aware view of a container and its position based view.

   procedure From_Model_To_Cursors (S : My_Sets.Set) with
     Ghost,
     Global => null,
     Pre    => (for all E of Model (S) => Q (E)),
     Post   => (for all Cu in S => Q (Element (S, Cu)));
   --  Test that the link can be done from a property on the elements of a
   --  high level view of a container and its lowest level, cursor aware view.

   procedure From_Cursors_To_Model (S : My_Sets.Set) with
     Ghost,
     Global => null,
     Pre    => (for all Cu in S => Q (Element (S, Cu))),
     Post   => (for all E of Model (S) => Q (E));
   --  Test that the link can be done from a property on the elements of a
   --  low level, cursor aware view of a container and its high level view.
end Use_Ordered_Sets;
