package Deep_Vectors is
   pragma Unevaluated_Use_Of_Old (Allow);
   type Int_Arr is array (Positive range <>) of Integer;
   type Int_Acc is access Integer;
   type Element_Type is record
      V : not null Int_Acc;
   end record;
   type Vector (C : Natural) is private with
     Aggregate => (Empty => Empty, Add_Unnamed => Add),
     Annotate  => (GNATprove, Container_Aggregates, "Predefined_Sequences");

   function Empty (C : Natural) return Vector;
   procedure Add (V : in out Vector; E : Element_Type) with
     Import,
     Always_Terminates,
     Global => null,
     Pre  => Length (V) < V.C,
     Post => Length (V) = Length (V)'Old + 1
     and then Int_Arr'(for I in 1 .. Length (V) => Get (V, I).V.all)'Old =
       (for I in 1 .. Length (V)'Old => Get (V, I).V.all)
       and then Get (V, Length (V)).V.all = E.V.all;

   function Length (V : Vector) return Natural with
     Annotate => (GNATprove, Container_Aggregates, "Last");
   function Get (V : Vector; I : Positive) return Element_Type with
     Annotate => (GNATprove, Container_Aggregates, "Get"),
     Pre => I <= Length (V);
   function First return Positive is (1) with
     Annotate => (GNATprove, Container_Aggregates, "First");
   function Capacity (V : Vector) return Natural is (V.C) with
     Annotate => (GNATprove, Container_Aggregates, "Capacity");

   procedure Clear (V : in out Vector) with
     Import,
     Always_Terminates,
     Global => null,
     Post => Length (V) = 0;
private
   type Element_Array is array (Positive range <>) of Int_Acc;
   type Vector (C : Natural) is record
      L : Natural := 0;
      A : Element_Array (1 .. C);
   end record with
     Predicate => L <= C
     and then (for all I in 1 .. C => (I > L) = (A (I) = null));

   function Copy (E : not null Int_Acc) return not null Int_Acc is
     (new Integer'(E.all));

   function Empty (C : Natural) return Vector is
     ((C => C, L => 0, A => (1 .. C => <>)));
   function Length (V : Vector) return Natural is (V.L);
   function Get (V : Vector; I : Positive) return Element_Type is
     (V => Copy (V.A (I)));
end Deep_Vectors;
