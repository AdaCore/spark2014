procedure Test_Illegal_Capacity with SPARK_Mode is

   --  Incorrect Capacity, no parameters with specific capacity

   package P1 is
      type Element_Type is new Integer;

      type T (Capacity : Natural) is private with
        Aggregate => (Empty       => Empty,
                      Add_Unnamed => Append),
        Annotate => (GNATprove, Container_Aggregates, "Predefined_Sets");

      function Empty (X : Natural) return T with
        Global => null;
      procedure Append (X : in out T; E : Element_Type) with
        Global => null,
        Pre => Length (X) < X.Capacity,
        Always_Terminates,
        Import;

      function Length (X : T) return Natural with
        Global => null,
        Annotate => (GNATprove, Container_Aggregates, "Length");

      function Capacity return Natural with
        Import,
        Global => null,
        Annotate => (GNATprove, Container_Aggregates, "Capacity");

      function Contains (X : T; E : Element_Type) return Boolean with
        Annotate => (GNATprove, Container_Aggregates, "Contains");

      function Eq_Element (X, Y : Element_Type) return Boolean is (X = Y) with
        Annotate => (GNATprove, Container_Aggregates, "Equivalent_Elements");

   private
      type T_Content is array (Positive range <>) of Element_Type with
        Relaxed_Initialization;

      type T (Capacity : Natural) is record
         Content : T_Content (1 .. Capacity);
         Top     : Natural;
      end record with
        Ghost_Predicate => Top <= Capacity
        and then (for all I in 1 .. Top => Content (I)'Initialized);

      function Contains (X : T; E : Element_Type) return Boolean is
        (for some I in 1 .. X.Top => X.Content (I) = E);
      function Length (X : T) return Natural is (X.Top);

      function Empty (X : Natural) return T is
        ((Capacity => X, Content => (others => <>), Top => 0));
   end P1;

   --  Incorrect Capacity, parameter with constant capacity

   package Q1 is
      Max : constant Natural := 100;
      type Element_Type is new Integer;

      type T is private with
        Aggregate => (Empty       => Empty,
                      Add_Unnamed => Append),
        Annotate => (GNATprove, Container_Aggregates, "Predefined_Sets");

      function Empty return T with
        Global => null;
      procedure Append (X : in out T; E : Element_Type) with
        Global => null,
        Pre => Length (X) < Max,
        Always_Terminates,
        Import;

      function Length (X : T) return Natural with
        Global => null,
        Annotate => (GNATprove, Container_Aggregates, "Length");

      function Capacity (X : T) return Natural is (Max) with
        Annotate => (GNATprove, Container_Aggregates, "Capacity");

      function Contains (X : T; E : Element_Type) return Boolean with
        Annotate => (GNATprove, Container_Aggregates, "Contains");

      function Eq_Element (X, Y : Element_Type) return Boolean is (X = Y) with
        Annotate => (GNATprove, Container_Aggregates, "Equivalent_Elements");

   private
      type T_Content is array (Positive range 1 .. Max) of Element_Type with
        Relaxed_Initialization;

      type T is record
         Content : T_Content;
         Top     : Natural;
      end record with
        Ghost_Predicate => Top <= Max
        and then (for all I in 1 .. Top => Content (I)'Initialized);

      function Contains (X : T; E : Element_Type) return Boolean is
        (for some I in 1 .. X.Top => X.Content (I) = E);
      function Length (X : T) return Natural is (X.Top);

      function Empty return T is
        ((Content => (others => <>), Top => 0));
   end Q1;

   --  Incorrect Capacity, bad first parameter with specific capacity

   package P2 is
      type Element_Type is new Integer;

      type T (Capacity : Natural) is private with
        Aggregate => (Empty       => Empty,
                      Add_Unnamed => Append),
        Annotate => (GNATprove, Container_Aggregates, "Predefined_Sets");

      function Empty (X : Natural) return T with
        Global => null;
      procedure Append (X : in out T; E : Element_Type) with
        Global => null,
        Pre => Length (X) < X.Capacity,
        Always_Terminates,
        Import;

      function Length (X : T) return Natural with
        Global => null,
        Annotate => (GNATprove, Container_Aggregates, "Length");

      function Capacity (X : Integer) return Natural with
        Import,
        Global => null,
        Annotate => (GNATprove, Container_Aggregates, "Capacity");

      function Contains (X : T; E : Element_Type) return Boolean with
        Annotate => (GNATprove, Container_Aggregates, "Contains");

      function Eq_Element (X, Y : Element_Type) return Boolean is (X = Y) with
        Annotate => (GNATprove, Container_Aggregates, "Equivalent_Elements");

   private
      type T_Content is array (Positive range <>) of Element_Type with
        Relaxed_Initialization;

      type T (Capacity : Natural) is record
         Content : T_Content (1 .. Capacity);
         Top     : Natural;
      end record with
        Ghost_Predicate => Top <= Capacity
        and then (for all I in 1 .. Top => Content (I)'Initialized);

      function Contains (X : T; E : Element_Type) return Boolean is
        (for some I in 1 .. X.Top => X.Content (I) = E);
      function Length (X : T) return Natural is (X.Top);

      function Empty (X : Natural) return T is
        ((Capacity => X, Content => (others => <>), Top => 0));
   end P2;

   --  Incorrect Capacity, bad number of parameters with specific capacity

   package P3 is
      type Element_Type is new Integer;

      type T (Capacity : Natural) is private with
        Aggregate => (Empty       => Empty,
                      Add_Unnamed => Append),
        Annotate => (GNATprove, Container_Aggregates, "Predefined_Sets");

      function Empty (X : Natural) return T with
        Global => null;
      procedure Append (X : in out T; E : Element_Type) with
        Global => null,
        Pre => Length (X) < X.Capacity,
        Always_Terminates,
        Import;

      function Length (X : T) return Natural with
        Global => null,
        Annotate => (GNATprove, Container_Aggregates, "Length");

      function Capacity (X : T; Y : Integer) return Natural with
        Import,
        Global => null,
        Annotate => (GNATprove, Container_Aggregates, "Capacity");

      function Contains (X : T; E : Element_Type) return Boolean with
        Annotate => (GNATprove, Container_Aggregates, "Contains");

      function Eq_Element (X, Y : Element_Type) return Boolean is (X = Y) with
        Annotate => (GNATprove, Container_Aggregates, "Equivalent_Elements");

   private
      type T_Content is array (Positive range <>) of Element_Type with
        Relaxed_Initialization;

      type T (Capacity : Natural) is record
         Content : T_Content (1 .. Capacity);
         Top     : Natural;
      end record with
        Ghost_Predicate => Top <= Capacity
        and then (for all I in 1 .. Top => Content (I)'Initialized);

      function Contains (X : T; E : Element_Type) return Boolean is
        (for some I in 1 .. X.Top => X.Content (I) = E);
      function Length (X : T) return Natural is (X.Top);

      function Empty (X : Natural) return T is
        ((Capacity => X, Content => (others => <>), Top => 0));
   end P3;

   --  Incorrect Capacity, noninteger return type

   package P4 is
      type Element_Type is new Integer;

      type T (Capacity : Natural) is private with
        Aggregate => (Empty       => Empty,
                      Add_Unnamed => Append),
        Annotate => (GNATprove, Container_Aggregates, "Predefined_Sets");

      function Empty (X : Natural) return T with
        Global => null;
      procedure Append (X : in out T; E : Element_Type) with
        Global => null,
        Pre => Length (X) < X.Capacity,
        Always_Terminates,
        Import;

      function Length (X : T) return Natural with
        Global => null,
        Annotate => (GNATprove, Container_Aggregates, "Length");

      function Capacity (X : T) return Boolean with
        Import,
        Global => null,
        Annotate => (GNATprove, Container_Aggregates, "Capacity");

      function Contains (X : T; E : Element_Type) return Boolean with
        Annotate => (GNATprove, Container_Aggregates, "Contains");

      function Eq_Element (X, Y : Element_Type) return Boolean is (X = Y) with
        Annotate => (GNATprove, Container_Aggregates, "Equivalent_Elements");

   private
      type T_Content is array (Positive range <>) of Element_Type with
        Relaxed_Initialization;

      type T (Capacity : Natural) is record
         Content : T_Content (1 .. Capacity);
         Top     : Natural;
      end record with
        Ghost_Predicate => Top <= Capacity
        and then (for all I in 1 .. Top => Content (I)'Initialized);

      function Contains (X : T; E : Element_Type) return Boolean is
        (for some I in 1 .. X.Top => X.Content (I) = E);
      function Length (X : T) return Natural is (X.Top);

      function Empty (X : Natural) return T is
        ((Capacity => X, Content => (others => <>), Top => 0));
   end P4;

   --  Incorrect Capacity, duplicate function

   package P5 is
      type Element_Type is new Integer;

      type T (Capacity : Natural) is private with
        Aggregate => (Empty       => Empty,
                      Add_Unnamed => Append),
        Annotate => (GNATprove, Container_Aggregates, "Predefined_Sets");

      function Empty (X : Natural) return T with
        Global => null;
      procedure Append (X : in out T; E : Element_Type) with
        Global => null,
        Pre => Length (X) < X.Capacity,
        Always_Terminates,
        Import;

      function Length (X : T) return Natural with
        Global => null,
        Annotate => (GNATprove, Container_Aggregates, "Length");

      function Capacity (X : T) return Natural with
        Import,
        Global => null,
        Annotate => (GNATprove, Container_Aggregates, "Capacity");

      function Capacity_2 (X : T) return Natural with
        Import,
        Global => null,
        Annotate => (GNATprove, Container_Aggregates, "Capacity");

      function Contains (X : T; E : Element_Type) return Boolean with
        Annotate => (GNATprove, Container_Aggregates, "Contains");

      function Eq_Element (X, Y : Element_Type) return Boolean is (X = Y) with
        Annotate => (GNATprove, Container_Aggregates, "Equivalent_Elements");

   private
      type T_Content is array (Positive range <>) of Element_Type with
        Relaxed_Initialization;

      type T (Capacity : Natural) is record
         Content : T_Content (1 .. Capacity);
         Top     : Natural;
      end record with
        Ghost_Predicate => Top <= Capacity
        and then (for all I in 1 .. Top => Content (I)'Initialized);

      function Contains (X : T; E : Element_Type) return Boolean is
        (for some I in 1 .. X.Top => X.Content (I) = E);
      function Length (X : T) return Natural is (X.Top);

      function Empty (X : Natural) return T is
        ((Capacity => X, Content => (others => <>), Top => 0));
   end P5;

   package Q2 is
      Max : constant Natural := 100;
      type Element_Type is new Integer;

      type T is private with
        Aggregate => (Empty       => Empty,
                      Add_Unnamed => Append),
        Annotate => (GNATprove, Container_Aggregates, "Predefined_Sets");

      function Empty return T with
        Global => null;
      procedure Append (X : in out T; E : Element_Type) with
        Global => null,
        Pre => Length (X) < Max,
        Always_Terminates,
        Import;

      function Length (X : T) return Natural with
        Global => null,
        Annotate => (GNATprove, Container_Aggregates, "Length");

      function Capacity return Natural with
        Import,
        Global => null,
        Annotate => (GNATprove, Container_Aggregates, "Capacity");

      function Capacity_2 return Natural with
        Import,
        Global => null,
        Annotate => (GNATprove, Container_Aggregates, "Capacity");

      function Contains (X : T; E : Element_Type) return Boolean with
        Annotate => (GNATprove, Container_Aggregates, "Contains");

      function Eq_Element (X, Y : Element_Type) return Boolean is (X = Y) with
        Annotate => (GNATprove, Container_Aggregates, "Equivalent_Elements");

   private
      type T_Content is array (Positive range 1 .. Max) of Element_Type with
        Relaxed_Initialization;

      type T is record
         Content : T_Content;
         Top     : Natural;
      end record with
        Ghost_Predicate => Top <= Max
        and then (for all I in 1 .. Top => Content (I)'Initialized);

      function Contains (X : T; E : Element_Type) return Boolean is
        (for some I in 1 .. X.Top => X.Content (I) = E);
      function Length (X : T) return Natural is (X.Top);

      function Empty return T is
        ((Content => (others => <>), Top => 0));
   end Q2;

   --  Incorrect Capacity, bad location

   package P6 is
      type Element_Type is new Integer;

      type T (Capacity : Natural) is private with
        Aggregate => (Empty       => Empty,
                      Add_Unnamed => Append),
        Annotate => (GNATprove, Container_Aggregates, "Predefined_Sets");

      function Empty (X : Natural) return T with
        Global => null;
      procedure Append (X : in out T; E : Element_Type) with
        Global => null,
        Pre => Length (X) < X.Capacity,
        Always_Terminates,
        Import;

      function Length (X : T) return Natural with
        Global => null,
        Annotate => (GNATprove, Container_Aggregates, "Length");

      package Nested is
         function Capacity (X : T) return Natural with
           Import,
           Global => null,
           Annotate => (GNATprove, Container_Aggregates, "Capacity");
      end Nested;

      function Contains (X : T; E : Element_Type) return Boolean with
        Annotate => (GNATprove, Container_Aggregates, "Contains");

      function Eq_Element (X, Y : Element_Type) return Boolean is (X = Y) with
        Annotate => (GNATprove, Container_Aggregates, "Equivalent_Elements");

   private
      type T_Content is array (Positive range <>) of Element_Type with
        Relaxed_Initialization;

      type T (Capacity : Natural) is record
         Content : T_Content (1 .. Capacity);
         Top     : Natural;
      end record with
        Ghost_Predicate => Top <= Capacity
        and then (for all I in 1 .. Top => Content (I)'Initialized);

      function Contains (X : T; E : Element_Type) return Boolean is
        (for some I in 1 .. X.Top => X.Content (I) = E);
      function Length (X : T) return Natural is (X.Top);

      function Empty (X : Natural) return T is
        ((Capacity => X, Content => (others => <>), Top => 0));
   end P6;

   --  ??? Here capacity is just not found

   package Q3 is
      Max : constant Natural := 100;
      type Element_Type is new Integer;

      type T is private with
        Aggregate => (Empty       => Empty,
                      Add_Unnamed => Append),
        Annotate => (GNATprove, Container_Aggregates, "Predefined_Sets");

      function Empty return T with
        Global => null;
      procedure Append (X : in out T; E : Element_Type) with
        Global => null,
        Pre => Length (X) < Max,
        Always_Terminates,
        Import;

      function Length (X : T) return Natural with
        Global => null,
        Annotate => (GNATprove, Container_Aggregates, "Length");

      package Nested is
         function Capacity return Natural with
           Import,
           Global => null,
           Annotate => (GNATprove, Container_Aggregates, "Capacity");
      end Nested;

      function Contains (X : T; E : Element_Type) return Boolean with
        Annotate => (GNATprove, Container_Aggregates, "Contains");

      function Eq_Element (X, Y : Element_Type) return Boolean is (X = Y) with
        Annotate => (GNATprove, Container_Aggregates, "Equivalent_Elements");

   private
      type T_Content is array (Positive range 1 .. Max) of Element_Type with
        Relaxed_Initialization;

      type T is record
         Content : T_Content;
         Top     : Natural;
      end record with
        Ghost_Predicate => Top <= Max
        and then (for all I in 1 .. Top => Content (I)'Initialized);

      function Contains (X : T; E : Element_Type) return Boolean is
        (for some I in 1 .. X.Top => X.Content (I) = E);
      function Length (X : T) return Natural is (X.Top);

      function Empty return T is
        ((Content => (others => <>), Top => 0));
   end Q3;

   --  Incorrect Capacity, bad location of annotate

   package P7 is
      type Element_Type is new Integer;

      type T (Capacity : Natural) is private with
        Aggregate => (Empty       => Empty,
                      Add_Unnamed => Append),
        Annotate => (GNATprove, Container_Aggregates, "Predefined_Sets");

      function Empty (X : Natural) return T with
        Global => null;
      procedure Append (X : in out T; E : Element_Type) with
        Global => null,
        Pre => Length (X) < X.Capacity,
        Always_Terminates,
        Import;

      function Length (X : T) return Natural with
        Global => null,
        Annotate => (GNATprove, Container_Aggregates, "Length");

      function Capacity (X : T) return Natural with
        Import,
        Global => null;

      function Contains (X : T; E : Element_Type) return Boolean with
        Annotate => (GNATprove, Container_Aggregates, "Contains");

      function Eq_Element (X, Y : Element_Type) return Boolean is (X = Y) with
        Annotate => (GNATprove, Container_Aggregates, "Equivalent_Elements");

      pragma Annotate (GNATprove, Container_Aggregates, "Capacity", Capacity);

   private
      type T_Content is array (Positive range <>) of Element_Type with
        Relaxed_Initialization;

      type T (Capacity : Natural) is record
         Content : T_Content (1 .. Capacity);
         Top     : Natural;
      end record with
        Ghost_Predicate => Top <= Capacity
        and then (for all I in 1 .. Top => Content (I)'Initialized);

      function Contains (X : T; E : Element_Type) return Boolean is
        (for some I in 1 .. X.Top => X.Content (I) = E);
      function Length (X : T) return Natural is (X.Top);

      function Empty (X : Natural) return T is
        ((Capacity => X, Content => (others => <>), Top => 0));
   end P7;

   package Q4 is
      Max : constant Natural := 100;
      type Element_Type is new Integer;

      type T is private with
        Aggregate => (Empty       => Empty,
                      Add_Unnamed => Append),
        Annotate => (GNATprove, Container_Aggregates, "Predefined_Sets");

      function Empty return T with
        Global => null;
      procedure Append (X : in out T; E : Element_Type) with
        Global => null,
        Pre => Length (X) < Max,
        Always_Terminates,
        Import;

      function Length (X : T) return Natural with
        Global => null,
        Annotate => (GNATprove, Container_Aggregates, "Length");

      function Capacity return Natural with
        Import,
        Global => null;

      function Contains (X : T; E : Element_Type) return Boolean with
        Annotate => (GNATprove, Container_Aggregates, "Contains");

      function Eq_Element (X, Y : Element_Type) return Boolean is (X = Y) with
        Annotate => (GNATprove, Container_Aggregates, "Equivalent_Elements");

      pragma Annotate (GNATprove, Container_Aggregates, "Capacity", Capacity);

   private
      type T_Content is array (Positive range 1 .. Max) of Element_Type with
        Relaxed_Initialization;

      type T is record
         Content : T_Content;
         Top     : Natural;
      end record with
        Ghost_Predicate => Top <= Max
        and then (for all I in 1 .. Top => Content (I)'Initialized);

      function Contains (X : T; E : Element_Type) return Boolean is
        (for some I in 1 .. X.Top => X.Content (I) = E);
      function Length (X : T) return Natural is (X.Top);

      function Empty return T is
        ((Content => (others => <>), Top => 0));
   end Q4;

   --  Incorrect Capacity, function with side effects

   package P8 is
      type Element_Type is new Integer;

      type T (Capacity : Natural) is private with
        Aggregate => (Empty       => Empty,
                      Add_Unnamed => Append),
        Annotate => (GNATprove, Container_Aggregates, "Predefined_Sets");

      function Empty (X : Natural) return T with
        Global => null;
      procedure Append (X : in out T; E : Element_Type) with
        Global => null,
        Pre => Length (X) < X.Capacity,
        Always_Terminates,
        Import;

      function Length (X : T) return Natural with
        Global => null,
        Annotate => (GNATprove, Container_Aggregates, "Length");

      function Capacity (X : T) return Natural with
        Side_Effects,
        Import,
        Global => null,
        Annotate => (GNATprove, Container_Aggregates, "Capacity");

      function Contains (X : T; E : Element_Type) return Boolean with
        Annotate => (GNATprove, Container_Aggregates, "Contains");

      function Eq_Element (X, Y : Element_Type) return Boolean is (X = Y) with
        Annotate => (GNATprove, Container_Aggregates, "Equivalent_Elements");

   private
      type T_Content is array (Positive range <>) of Element_Type with
        Relaxed_Initialization;

      type T (Capacity : Natural) is record
         Content : T_Content (1 .. Capacity);
         Top     : Natural;
      end record with
        Ghost_Predicate => Top <= Capacity
        and then (for all I in 1 .. Top => Content (I)'Initialized);

      function Contains (X : T; E : Element_Type) return Boolean is
        (for some I in 1 .. X.Top => X.Content (I) = E);
      function Length (X : T) return Natural is (X.Top);

      function Empty (X : Natural) return T is
        ((Capacity => X, Content => (others => <>), Top => 0));
   end P8;

   --  Incorrect Capacity, volatile function

   package Q5 is
      Max : constant Natural := 100;
      type Element_Type is new Integer;

      type T is private with
        Aggregate => (Empty       => Empty,
                      Add_Unnamed => Append),
        Annotate => (GNATprove, Container_Aggregates, "Predefined_Sets");

      function Empty return T with
        Global => null;
      procedure Append (X : in out T; E : Element_Type) with
        Global => null,
        Pre => Length (X) < Max,
        Always_Terminates,
        Import;

      function Length (X : T) return Natural with
        Global => null,
        Annotate => (GNATprove, Container_Aggregates, "Length");

      function Capacity return Natural with
        Volatile_Function,
        Import,
        Global => null,
        Annotate => (GNATprove, Container_Aggregates, "Capacity");

      function Contains (X : T; E : Element_Type) return Boolean with
        Annotate => (GNATprove, Container_Aggregates, "Contains");

      function Eq_Element (X, Y : Element_Type) return Boolean is (X = Y) with
        Annotate => (GNATprove, Container_Aggregates, "Equivalent_Elements");

   private
      type T_Content is array (Positive range 1 .. Max) of Element_Type with
        Relaxed_Initialization;

      type T is record
         Content : T_Content;
         Top     : Natural;
      end record with
        Ghost_Predicate => Top <= Max
        and then (for all I in 1 .. Top => Content (I)'Initialized);

      function Contains (X : T; E : Element_Type) return Boolean is
        (for some I in 1 .. X.Top => X.Content (I) = E);
      function Length (X : T) return Natural is (X.Top);

      function Empty return T is
        ((Content => (others => <>), Top => 0));
   end Q5;

   --  Incorrect Capacity, SPARK_Mode => Off

   package P9 is
      type Element_Type is new Integer;

      type T (Capacity : Natural) is private with
        Aggregate => (Empty       => Empty,
                      Add_Unnamed => Append),
        Annotate => (GNATprove, Container_Aggregates, "Predefined_Sets");

      function Empty (X : Natural) return T with
        Global => null;
      procedure Append (X : in out T; E : Element_Type) with
        Global => null,
        Pre => Length (X) < X.Capacity,
        Always_Terminates,
        Import;

      function Length (X : T) return Natural with
        Global => null,
        Annotate => (GNATprove, Container_Aggregates, "Length");

      function Capacity (X : T) return Natural with
        SPARK_Mode => Off,
        Import,
        Global => null,
        Annotate => (GNATprove, Container_Aggregates, "Capacity");

      function Contains (X : T; E : Element_Type) return Boolean with
        Annotate => (GNATprove, Container_Aggregates, "Contains");

      function Eq_Element (X, Y : Element_Type) return Boolean is (X = Y) with
        Annotate => (GNATprove, Container_Aggregates, "Equivalent_Elements");

   private
      type T_Content is array (Positive range <>) of Element_Type with
        Relaxed_Initialization;

      type T (Capacity : Natural) is record
         Content : T_Content (1 .. Capacity);
         Top     : Natural;
      end record with
        Ghost_Predicate => Top <= Capacity
        and then (for all I in 1 .. Top => Content (I)'Initialized);

      function Contains (X : T; E : Element_Type) return Boolean is
        (for some I in 1 .. X.Top => X.Content (I) = E);
      function Length (X : T) return Natural is (X.Top);

      function Empty (X : Natural) return T is
        ((Capacity => X, Content => (others => <>), Top => 0));
   end P9;

   --  ??? Here capacity is just not found

   package Q6 is
      Max : constant Natural := 100;
      type Element_Type is new Integer;

      type T is private with
        Aggregate => (Empty       => Empty,
                      Add_Unnamed => Append),
        Annotate => (GNATprove, Container_Aggregates, "Predefined_Sets");

      function Empty return T with
        Global => null;
      procedure Append (X : in out T; E : Element_Type) with
        Global => null,
        Pre => Length (X) < Max,
        Always_Terminates,
        Import;

      function Length (X : T) return Natural with
        Global => null,
        Annotate => (GNATprove, Container_Aggregates, "Length");

      function Capacity return Natural with
        SPARK_Mode => Off,
        Import,
        Global => null,
        Annotate => (GNATprove, Container_Aggregates, "Capacity");

      function Contains (X : T; E : Element_Type) return Boolean with
        Annotate => (GNATprove, Container_Aggregates, "Contains");

      function Eq_Element (X, Y : Element_Type) return Boolean is (X = Y) with
        Annotate => (GNATprove, Container_Aggregates, "Equivalent_Elements");

   private
      type T_Content is array (Positive range 1 .. Max) of Element_Type with
        Relaxed_Initialization;

      type T is record
         Content : T_Content;
         Top     : Natural;
      end record with
        Ghost_Predicate => Top <= Max
        and then (for all I in 1 .. Top => Content (I)'Initialized);

      function Contains (X : T; E : Element_Type) return Boolean is
        (for some I in 1 .. X.Top => X.Content (I) = E);
      function Length (X : T) return Natural is (X.Top);

      function Empty return T is
        ((Content => (others => <>), Top => 0));
   end Q6;

   --  Incorrect Capacity, global access

   package Q7 is
      Max : constant Natural := 100;
      type Element_Type is new Integer;

      type T is private with
        Aggregate => (Empty       => Empty,
                      Add_Unnamed => Append),
        Annotate => (GNATprove, Container_Aggregates, "Predefined_Sets");

      function Empty return T with
        Global => null;
      procedure Append (X : in out T; E : Element_Type) with
        Global => null,
        Pre => Length (X) < Max,
        Always_Terminates,
        Import;

      function Length (X : T) return Natural with
        Global => null,
        Annotate => (GNATprove, Container_Aggregates, "Length");

      X : Integer;

      function Capacity return Natural with
        Import,
        Global => X,
        Annotate => (GNATprove, Container_Aggregates, "Capacity");

      function Contains (X : T; E : Element_Type) return Boolean with
        Annotate => (GNATprove, Container_Aggregates, "Contains");

      function Eq_Element (X, Y : Element_Type) return Boolean is (X = Y) with
        Annotate => (GNATprove, Container_Aggregates, "Equivalent_Elements");

   private
      type T_Content is array (Positive range 1 .. Max) of Element_Type with
        Relaxed_Initialization;

      type T is record
         Content : T_Content;
         Top     : Natural;
      end record with
        Ghost_Predicate => Top <= Max
        and then (for all I in 1 .. Top => Content (I)'Initialized);

      function Contains (X : T; E : Element_Type) return Boolean is
        (for some I in 1 .. X.Top => X.Content (I) = E);
      function Length (X : T) return Natural is (X.Top);

      function Empty return T is
        ((Content => (others => <>), Top => 0));
   end Q7;

   --  Specific capacity is not checked if T is not in SPARK

   package P10 is
      type Element_Type is new Integer;

      package Nested with SPARK_Mode => Off is
	 subtype Bad is Natural;
      end Nested;

      type T (Capacity : Nested.Bad) is private with
        Aggregate => (Empty       => Empty,
                      Add_Unnamed => Append),
        Annotate => (GNATprove, Container_Aggregates, "Predefined_Sets");

      function Empty (X : Natural) return T with
	SPARK_Mode => Off,
        Global => null,
        Import;
      procedure Append (X : in out T; E : Element_Type) with
	SPARK_Mode => Off,
        Global => null,
        Always_Terminates,
        Import;

      function Capacity (X : T) return Natural is (X.Capacity) with
	SPARK_Mode => Off,
        Annotate => (GNATprove, Container_Aggregates, "Capacity");

   private
      type T_Content is array (Positive range <>) of Element_Type with
        Relaxed_Initialization;

      type T (Capacity : Nested.Bad) is record
         Content : T_Content (1 .. 10);
         Top     : Natural;
      end record;
   end P10;

   --  OK with specific capacity

   package P11 is
      type Element_Type is new Integer;

      type T (Capacity : Natural) is private with
        Aggregate => (Empty       => Empty,
                      Add_Unnamed => Append),
        Annotate => (GNATprove, Container_Aggregates, "Predefined_Sets");

      function Empty (X : Natural) return T with
        Global => null;
      procedure Append (X : in out T; E : Element_Type) with
        Global => null,
        Pre => Length (X) < X.Capacity,
        Always_Terminates,
        Import;

      function Length (X : T) return Natural with
        Global => null,
        Annotate => (GNATprove, Container_Aggregates, "Length");

      function Capacity (X : T) return Natural is (X.Capacity) with
        Annotate => (GNATprove, Container_Aggregates, "Capacity");

      function Contains (X : T; E : Element_Type) return Boolean with
        Annotate => (GNATprove, Container_Aggregates, "Contains");

      function Eq_Element (X, Y : Element_Type) return Boolean is (X = Y) with
        Annotate => (GNATprove, Container_Aggregates, "Equivalent_Elements");

   private
      type T_Content is array (Positive range <>) of Element_Type with
        Relaxed_Initialization;

      type T (Capacity : Natural) is record
         Content : T_Content (1 .. Capacity);
         Top     : Natural;
      end record with
        Ghost_Predicate => Top <= Capacity
        and then (for all I in 1 .. Top => Content (I)'Initialized);

      function Contains (X : T; E : Element_Type) return Boolean is
        (for some I in 1 .. X.Top => X.Content (I) = E);
      function Length (X : T) return Natural is (X.Top);

      function Empty (X : Natural) return T is
        ((Capacity => X, Content => (others => <>), Top => 0));
   end P11;

   --  OK with constant capacity

   package Q8 is
      Max : constant Natural := 100;
      type Element_Type is new Integer;

      type T is private with
        Aggregate => (Empty       => Empty,
                      Add_Unnamed => Append),
        Annotate => (GNATprove, Container_Aggregates, "Predefined_Sets");

      function Empty return T with
        Global => null;
      procedure Append (X : in out T; E : Element_Type) with
        Global => null,
        Pre => Length (X) < Max,
        Always_Terminates,
        Import;

      function Length (X : T) return Natural with
        Global => null,
        Annotate => (GNATprove, Container_Aggregates, "Length");

      function Capacity return Natural is (Max) with
        Annotate => (GNATprove, Container_Aggregates, "Capacity");

      function Contains (X : T; E : Element_Type) return Boolean with
        Annotate => (GNATprove, Container_Aggregates, "Contains");

      function Eq_Element (X, Y : Element_Type) return Boolean is (X = Y) with
        Annotate => (GNATprove, Container_Aggregates, "Equivalent_Elements");

   private
      type T_Content is array (Positive range 1 .. Max) of Element_Type with
        Relaxed_Initialization;

      type T is record
         Content : T_Content;
         Top     : Natural;
      end record with
        Ghost_Predicate => Top <= Max
        and then (for all I in 1 .. Top => Content (I)'Initialized);

      function Contains (X : T; E : Element_Type) return Boolean is
        (for some I in 1 .. X.Top => X.Content (I) = E);
      function Length (X : T) return Natural is (X.Top);

      function Empty return T is
        ((Content => (others => <>), Top => 0));
   end Q8;

begin
   null;
end Test_Illegal_Capacity;
