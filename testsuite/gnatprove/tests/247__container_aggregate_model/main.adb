with SPARK.Big_Integers; use SPARK.Big_Integers;
with SPARK.Containers.Functional.Vectors;
with SPARK.Containers.Functional.Sets;
with SPARK.Containers.Functional.Maps;

procedure Main with SPARK_Mode is

   pragma Unevaluated_Use_Of_Old (Allow);

   package Seqs is
      type Index_Type is new Integer range 1 .. 10;
      subtype Ext_Index is Index_Type'Base range 0 .. 10;

      type Element_Type is new Integer;

      package Element_Vects is new SPARK.Containers.Functional.Vectors
        (Index_Type, Element_Type);
      use Element_Vects;

      type T is private with
        Aggregate => (Empty       => Empty,
                      Add_Unnamed => Append),
        Annotate => (GNATprove, Container_Aggregates, "From_Model");

      function Model (X : T) return Sequence with
        Global => null,
        Import,
        Annotate => (GNATprove, Container_Aggregates, "Model");

      function Empty return T with
        Global => null,
        Import,
        Post => Last (Model (Empty'Result)) = 0;

      procedure Append (X : in out T; E : Element_Type) with
        Global => null,
        Import,
        Always_Terminates,
        Pre => Last (Model (X)) < 10,
        Post => Last (Model (X)) = Last (Model (X))'Old + 1
        and then Get (Model (X), Last (Model (X))) = E
        and then (for all I in 1 .. Last (Model (X)) - 1 =>
                    Get (Model (X), I) =  Get (Model (X)'Old, I));

   private
      type T_Content is array (Index_Type) of Element_Type with
        Relaxed_Initialization;
      type T is record
         Content : T_Content;
         Top     : Ext_Index;
      end record with
        Ghost_Predicate =>
          (for all I in 1 .. Top => Content (I)'Initialized);
   end Seqs;

   package Sets is
      type Element_Type is new Integer;

      package Element_Sets is new SPARK.Containers.Functional.Sets
        (Element_Type);
      use Element_Sets;

      type T (Capacity : Natural) is private with
        Aggregate => (Empty       => Empty,
                      Add_Unnamed => Insert),
        Annotate => (GNATprove, Container_Aggregates, "From_Model");

      function Capacity (X : T) return Natural is (X.Capacity) with
        Annotate => (GNATprove, Container_Aggregates, "Capacity");

      function Model (X : T) return Set with
        Global => null,
        Import,
        Annotate => (GNATprove, Container_Aggregates, "Model");

      function Empty (Capacity : Natural) return T with
        Global => null,
        Post => Empty'Result.Capacity = Capacity
        and then Length (Model (Empty'Result)) = 0
        and then (for all F in Element_Type =>
                    not Contains (Model (Empty'Result), F)),
        Import;
      procedure Insert (X : in out T; E : Element_Type) with
        Global => null,
        Import,
        Always_Terminates,
        Post =>
          (if Contains (Model (X), E)'Old
           then Length (Model (X)) = Length (Model (X))'Old
           else Length (Model (X)) = Length (Model (X))'Old + 1)
        and then Contains (Model (X), E)
        and then (for all F in Element_Type =>
                    (if F /= E then Contains (Model (X), F) = Contains (Model (X)'Old, F)));

   private
      type T_Content is array (Positive range <>) of Element_Type with
        Relaxed_Initialization;
      type T (Capacity : Natural) is record
         Content : T_Content (1 .. Capacity);
         Top     : Natural;
      end record with
        Ghost_Predicate => Top <= Capacity
        and then (for all I in 1 .. Top => Content (I)'Initialized);
   end Sets;

   package Partial_Maps is
      type Key_Type is new Integer;
      type Element_Type is new Integer;

      package Key_To_Element_Maps is new SPARK.Containers.Functional.Maps
        (Key_Type, Element_Type);
      use Key_To_Element_Maps;

      type T is private with
        Aggregate => (Empty       => Empty,
                      Add_Named => Insert),
        Annotate => (GNATprove, Container_Aggregates, "From_Model");

      function Model (X : T) return Map with
        Global => null,
        Import,
        Annotate => (GNATprove, Container_Aggregates, "Model");

      function Empty return T with
        Global => null,
        Post => Length (Model (Empty'Result)) = 0
        and then (for all L in Key_Type =>
                    not Has_Key (Model (Empty'Result), L)),
        Import;
      procedure Insert (X : in out T; K : Key_Type; E : Element_Type) with
        Import,
        Always_Terminates,
        Pre  => not Has_Key (Model (X), K),
        Post => Length (Model (X)) = Length (Model (X))'Old + 1
        and then Has_Key (Model (X), K)
        and then Get (Model (X), K) = E
        and then (for all L in Key_Type =>
                    (if L /= K then Has_Key (Model (X), L) = Has_Key (Model (X)'Old, L)))
        and then (for all L in Key_Type =>
                    (if L /= K and Has_Key (Model (X), L) then
                         Get (Model (X), L) = Get (Model (X)'Old, L)));

   private
      type Pair is record
         K : Key_Type;
         E : Element_Type;
      end record;
      type T_Cell;
      type T is access T_Cell;
      type T_Cell is record
         P : Pair;
         N : T;
      end record;
   end Partial_Maps;

   package Total_Maps is
      type Key_Type is range 1 .. 100;
      type Element_Type is new Integer;

      package Key_To_Element_Total_Maps is
         type Map is private with
           Aggregate => (Empty       => Empty,
                         Add_Named   => Insert),
           Annotate => (GNATprove, Container_Aggregates, "Predefined_Maps");

         function Empty return Map;
         procedure Insert (X : in out Map; K : Key_Type; E : Element_Type) with
           Import,
           Always_Terminates,
           Post => Get (X, K) = E
           and then (for all L in Key_Type =>
                       (if L /= K then Get (X, L) = Get (X'Old, L)));

         function Default_Value return Element_Type is (0) with
           Annotate => (GNATprove, Container_Aggregates, "Default_Item");

         function Get (X : Map; K : Key_Type) return Element_Type with
           Annotate => (GNATprove, Container_Aggregates, "Get");

         function Eq_Key (X, Y : Key_Type) return Boolean is (X = Y) with
           Annotate => (GNATprove, Container_Aggregates, "Equivalent_Keys");

      private
         package Key_To_Element_Maps is new SPARK.Containers.Functional.Maps
           (Key_Type, Element_Type);
         use Key_To_Element_Maps;

         type Map is new Key_To_Element_Maps.Map;

         function Get (X : Map; K : Key_Type) return Element_Type is
           (if Has_Key (X, K) then Get (Key_To_Element_Maps.Map (X), K)
            else Default_Value);
         function Empty return Map is (Empty_Map);
      end Key_To_Element_Total_Maps;
      use Key_To_Element_Total_Maps;

      type T is private with
        Aggregate => (Empty       => Empty,
                      Add_Named => Insert),
        Annotate => (GNATprove, Container_Aggregates, "From_Model");

      function Model (X : T) return Map with
        Global => null,
        Import,
        Annotate => (GNATprove, Container_Aggregates, "Model");

      function Empty return T with
        Global => null,
        Post => (for all L in Key_Type =>
                    Get (Model (Empty'Result), L) = Default_Value),
        Import;
      procedure Insert (X : in out T; K : Key_Type; E : Element_Type) with
        Import,
        Always_Terminates,
        Post => Get (Model (X), K) = E
        and then (for all L in Key_Type =>
                    (if L /= K then
                         Get (Model (X), L) = Get (Model (X)'Old, L)));
   private
      type Pair is record
         K : Key_Type;
         E : Element_Type;
      end record;
      type T_Cell;
      type T is access T_Cell;
      type T_Cell is record
         P : Pair;
         N : T;
      end record;
   end Total_Maps;

   procedure Test_Sets (E : Sets.Element_Type) with
     Global => null;

   procedure Test_Sets (E : Sets.Element_Type) is
      use Sets;
      use Sets.Element_Sets;
      X : T := [1, 2, 3, 4, 5];
      Y : T := [];
      Z : T := [1, 2, 3, 2, 5];
   begin
      pragma Assert (Length (Model (X)) = 5);
      pragma Assert (Contains (Model (X), E) = (E in 1 | 2 | 3 | 4 | 5));
      pragma Assert (Length (Model (Y)) = 0);
      pragma Assert (not Contains (Model (Y), E));
      pragma Assert (Length (Model (Z)) < 5);
      pragma Assert (Contains (Model (Z), E) = (E in 1 | 2 | 3 | 5));
      pragma Assert (False); --  @ASSERT:FAIL
   end Test_Sets;

   procedure Test_Partial_Maps (K : Partial_Maps.Key_Type) with
     Global => null;

   procedure Test_Partial_Maps (K : Partial_Maps.Key_Type)  is
      use Partial_Maps;
      use Partial_Maps.Key_To_Element_Maps;
      X : T := [1 => 1, 2 => 2, 3 => 3, 4 => 4, 5 => 5];
      Y : T := [];
   begin
      pragma Assert (Length (Model (X)) = 5);
      pragma Assert (Has_Key (Model (X), K) = (K in 1 | 2 | 3 | 4 | 5));
      for I in Key_Type range 1 .. 5 loop
         pragma Assert (Get (Model (X), I) = Element_Type (I));
      end loop;
      pragma Assert (Length (Model (Y)) = 0);
      pragma Assert (not Has_Key (Model (Y), K));
      pragma Assert (False); --  @ASSERT:FAIL
   end Test_Partial_Maps;

   procedure Test_Bad_Partial_Maps with
     Global => null;

   procedure Test_Bad_Partial_Maps  is
      use Partial_Maps;
      X : T := [1 => 1, 2 => 2, 3 => 3, 4 => 4, 5 => 5, 2 => 2]; -- @PRECONDITION:FAIL
   begin
      null;
   end Test_Bad_Partial_Maps;

   procedure Test_Total_Maps (K : Total_Maps.Key_Type) with
     Global => null;

   procedure Test_Total_Maps (K : Total_Maps.Key_Type)  is
      use Total_Maps;
      use Total_Maps.Key_To_Element_Total_Maps;
      X : T := [1 => 1, 2 => 2, 3 => 3, 4 => 4, 5 => 5];
      Y : T := [];
   begin
      for I in Key_Type range 1 .. 5 loop
         pragma Assert (Get (Model (X), I) = Element_Type (I));
      end loop;
      pragma Assert (if K not in 1 | 2 | 3 | 4 | 5 then Get (Model (X), K) = 0);
      pragma Assert (Get (Model (Y), K) = 0);
      pragma Assert (False); --  @ASSERT:FAIL
   end Test_Total_Maps;

   procedure Test_Bad_Total_Maps with
     Global => null;

   procedure Test_Bad_Total_Maps  is
      use Partial_Maps;
      X : T := [1 => 1, 2 => 2, 3 => 3, 1 => 4, 5 => 5]; -- @PRECONDITION:FAIL
   begin
      null;
   end Test_Bad_Total_Maps;

   procedure Test_Seqs with
     Global => null;

   procedure Test_Seqs is
      use Seqs;
      use Seqs.Element_Vects;
      X : T := [1, 2, 3, 4, 5];
      Y : T := [];
   begin
      pragma Assert (Last (Model (X)) = 5);
      for I in Index_Type range 1 .. 5 loop
         pragma Assert (Get (Model (X), I) = Element_Type (I));
      end loop;
      pragma Assert (Last (Model (Y)) = 0);
      pragma Assert (False); --  @ASSERT:FAIL
   end Test_Seqs;

   procedure Test_Bad_Seqs with
     Global => null;

   procedure Test_Bad_Seqs is
      use Seqs;
      X : T := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]; -- @PRECONDITION:FAIL
   begin
      null;
   end Test_Bad_Seqs;

begin
   null;
end Main;
