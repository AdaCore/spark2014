with Conts.Lists.Indefinite_Unbounded_SPARK;
with Functional_Sequences;

generic
   type Element_Type is private;
   with function "=" (E1, E2 : Element_Type) return Boolean;
package Formal_Doubly_Linked_Lists with SPARK_Mode is
   package Element_Lists is new Conts.Lists.Indefinite_Unbounded_SPARK
     (Element_Type => Element_Type);
   type Cursor is new Element_Lists.Cursor;

   type List is tagged limited private with
     Default_Initial_Condition => Length (List) = 0;

   function Capacity (L : List'Class) return Natural;

   function Length (L : List'Class) return Natural with
     Post => Length'Result < Capacity (L);

   package Model is
      package Cursor_Sequence is new Functional_Sequences
        (Element_Type => Cursor,
         "="          => "=");
      package Element_Sequence is new Functional_Sequences
        (Element_Type => Element_Type,
         "="          => "=");
      use type Element_Sequence.Sequence;
      use type Cursor_Sequence.Sequence;

      function Get_Cursor_Model (L : List'Class) return
        Cursor_Sequence.Sequence with
        Post => Cursor_Sequence.Length (Get_Cursor_Model'Result) =
        Natural (Length (L))
        and then (for all N in 0 .. Natural (Length (L)) - 1 =>
                    Cursor_Sequence.Find
                      (Get_Cursor_Model'Result,
                       Cursor_Sequence.Get
                         (Get_Cursor_Model'Result, N)) = N);
      function Get_Element_Model (L : List'Class) return
        Element_Sequence.Sequence with
        Post => Element_Sequence.Length (Get_Element_Model'Result) =
        Natural (Length (L));
   end Model;
   use Model;
   use type Element_Sequence.Sequence;
   use type Cursor_Sequence.Sequence;

   function Element (L : List'Class; C : Cursor) return Element_Type with
     Pre  => Cursor_Sequence.Find (Get_Cursor_Model (L), C) >= 0,
     Post => Element'Result =
       Element_Sequence.Get (Get_Element_Model (L),
                             Cursor_Sequence.Find (Get_Cursor_Model (L), C));

   function First (L : List'Class) return Cursor with
     Post => (if Length (L) = 0
              then Cursor_Sequence.Find
                (Get_Cursor_Model (L), First'Result) = -1
              else First'Result = Cursor_Sequence.Get
                (Get_Cursor_Model (L), 0));

   procedure Next (L : List'Class; C : in out Cursor) with
     Pre  => Cursor_Sequence.Find (Get_Cursor_Model (L), C) >= 0,
     Post => (if Natural (Length (L)) =
                Cursor_Sequence.Find (Get_Cursor_Model (L), C'Old) + 1
              then Cursor_Sequence.Find (Get_Cursor_Model (L), C) = -1
              else Cursor_Sequence.Find (Get_Cursor_Model (L), C) =
                  Cursor_Sequence.Find (Get_Cursor_Model (L), C'Old) + 1);

   function Has_Element (L : List'Class; C : Cursor) return Boolean with
     Post => Has_Element'Result =
       (Cursor_Sequence.Find (Get_Cursor_Model (L), C) >= 0);

   procedure Append (L : in out List'Class; E : Element_Type)
   with
     Pre  => Length (L) <= Capacity (L) - 1,
     Post =>  Capacity (L) = Capacity (L)'Old
     and then Length (L) = Length (L)'Old + 1
     and then Get_Cursor_Model (L) =
     Cursor_Sequence.Snoc (Get_Cursor_Model (L)'Old,
                           Cursor_Sequence.Get
                             (Get_Cursor_Model (L), Length (L)))
     and then Get_Element_Model (L) =
     Element_Sequence.Snoc (Get_Element_Model (L)'Old,  E);

   procedure Clear (L : in out List'Class)
   with
       Post => Capacity (L) = Capacity (L)'Old
     and then Length (L) = 0;

private
   pragma SPARK_Mode (Off);

   type List is new Element_Lists.List with null record;

end Formal_Doubly_Linked_Lists;
