package Acc_Vectors with SPARK_Mode is
   pragma Unevaluated_Use_Of_Old (Allow);
   type Int_Arr is array (Positive range <>) of Integer;
   type Int_Acc is access Integer;
   subtype Element_Type is not null Int_Acc;
   type Vector (C : Natural) is private with
     Aggregate => (Empty => Empty, Add_Unnamed => Add),
     Annotate  => (GNATprove, Container_Aggregates, "Predefined_Sequences");
   --  Containers containing access-to-variable elements are not allowed as
   --  Add's profile allows modifying its IN parameters.

   function Empty (C : Natural) return Vector;
   procedure Add (V : in out Vector; E : Element_Type) with
     Import,
     Always_Terminates,
     Global => null,
     Pre  => Length (V) < V.C,
     Post => Length (V) = Length (V)'Old + 1
     and then Int_Arr'(for I in 1 .. Length (V) => Get (V, I).all)'Old =
       (for I in 1 .. Length (V)'Old => Get (V, I).all)
       and then Get (V, Length (V)).all = E.all;

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
     (Copy (V.A (I)));
end Acc_Vectors;
