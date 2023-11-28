procedure Test_Sequences with SPARK_Mode is

   --  OK

  package P1 is
      Max : constant := 100;
      type Index_Type is new Integer range 1 .. Max;
      subtype Ext_Index is Index_Type'Base range 0 .. Max;

      type Element_Type is private;

      type T is private with
        Aggregate => (Empty       => Empty,
                      Add_Unnamed => Append),
        Annotate => (GNATprove, Container_Aggregates, "Predefined_Sequences"); --@CONTAINER_AGGR_ANNOTATION:PASS

      function Empty return T with
        Global => null,
        Import,
        Post => Last (Empty'Result) = First - 1;
      procedure Append (X : in out T; E : Element_Type) with
        Global => null,
        Always_Terminates,
        Pre => Last (X) < Max,
        Post => Last (X) = Last (X)'Old + 1
        and then Get (X, Last (X)) = E
        and then (for all I in First .. Last (X) - 1 =>
                    Get (X, I) = Get (X'Old, I)),
        Import;

      function Get (X : T; I : Index_Type) return Element_Type with
        Annotate => (GNATprove, Container_Aggregates, "Get"),
        Pre => I <= Last (X),
        Global => null,
        Import;

      function Last (X : T) return Ext_Index with
        Annotate => (GNATprove, Container_Aggregates, "Last"),
        Global => null,
        Import;

      function First return Index_Type with
        Annotate => (GNATprove, Container_Aggregates, "First"),
        Global => null,
        Import;

   private
      pragma SPARK_Mode (Off);
      type Element_Type is new Integer;
      type T is new Integer;
   end P1;

   --  Missing post on Last on Empty

  package P2 is
      Max : constant := 100;
      type Index_Type is new Integer range 1 .. Max;
      subtype Ext_Index is Index_Type'Base range 0 .. Max;

      type Element_Type is private;

      type T is private with
        Aggregate => (Empty       => Empty,
                      Add_Unnamed => Append),
        Annotate => (GNATprove, Container_Aggregates, "Predefined_Sequences"); --@CONTAINER_AGGR_ANNOTATION:FAIL

      function Empty return T with
        Global => null,
        Import;
      procedure Append (X : in out T; E : Element_Type) with
        Global => null,
        Always_Terminates,
        Pre => Last (X) < Max,
        Post => Last (X) = Last (X)'Old + 1
        and then Get (X, Last (X)) = E
        and then (for all I in First .. Last (X) - 1 =>
                    Get (X, I) = Get (X'Old, I)),
        Import;

      function Get (X : T; I : Index_Type) return Element_Type with
        Annotate => (GNATprove, Container_Aggregates, "Get"),
        Pre => I <= Last (X),
        Global => null,
        Import;

      function Last (X : T) return Ext_Index with
        Annotate => (GNATprove, Container_Aggregates, "Last"),
        Global => null,
        Import;

      function First return Index_Type with
        Annotate => (GNATprove, Container_Aggregates, "First"),
        Global => null,
        Import;

   private
      pragma SPARK_Mode (Off);
      type Element_Type is new Integer;
      type T is new Integer;
   end P2;

   --  Missing post on Last on Insert

  package P3 is
      Max : constant := 100;
      type Index_Type is new Integer range 1 .. Max;
      subtype Ext_Index is Index_Type'Base range 0 .. Max;

      type Element_Type is private;

      type T is private with
        Aggregate => (Empty       => Empty,
                      Add_Unnamed => Append),
        Annotate => (GNATprove, Container_Aggregates, "Predefined_Sequences"); --@CONTAINER_AGGR_ANNOTATION:FAIL

      function Empty return T with
        Global => null,
        Import,
        Post => Last (Empty'Result) = First - 1;
      procedure Append (X : in out T; E : Element_Type) with
        Global => null,
        Always_Terminates,
        Pre => Last (X) < Max,
        Post => Get (X, Last (X)) = E
        and then (for all I in First .. Last (X) - 1 =>
                    Get (X, I) = Get (X'Old, I)),
        Import;

      function Get (X : T; I : Index_Type) return Element_Type with
        Annotate => (GNATprove, Container_Aggregates, "Get"),
        Pre => I <= Last (X),
        Global => null,
        Import;

      function Last (X : T) return Ext_Index with
        Annotate => (GNATprove, Container_Aggregates, "Last"),
        Global => null,
        Import;

      function First return Index_Type with
        Annotate => (GNATprove, Container_Aggregates, "First"),
        Global => null,
        Import;

   private
      pragma SPARK_Mode (Off);
      type Element_Type is new Integer;
      type T is new Integer;
   end P3;

   --  Missing post on Get for last index on Insert

  package P4 is
      Max : constant := 100;
      type Index_Type is new Integer range 1 .. Max;
      subtype Ext_Index is Index_Type'Base range 0 .. Max;

      type Element_Type is private;

      type T is private with
        Aggregate => (Empty       => Empty,
                      Add_Unnamed => Append),
        Annotate => (GNATprove, Container_Aggregates, "Predefined_Sequences"); --@CONTAINER_AGGR_ANNOTATION:FAIL

      function Empty return T with
        Global => null,
        Import,
        Post => Last (Empty'Result) = First - 1;
      procedure Append (X : in out T; E : Element_Type) with
        Global => null,
        Always_Terminates,
        Pre => Last (X) < Max,
        Post => Last (X) = Last (X)'Old + 1
        and then (for all I in First .. Last (X) - 1 =>
                    Get (X, I) = Get (X'Old, I)),
        Import;

      function Get (X : T; I : Index_Type) return Element_Type with
        Annotate => (GNATprove, Container_Aggregates, "Get"),
        Pre => I <= Last (X),
        Global => null,
        Import;

      function Last (X : T) return Ext_Index with
        Annotate => (GNATprove, Container_Aggregates, "Last"),
        Global => null,
        Import;

      function First return Index_Type with
        Annotate => (GNATprove, Container_Aggregates, "First"),
        Global => null,
        Import;

   private
      pragma SPARK_Mode (Off);
      type Element_Type is new Integer;
      type T is new Integer;
   end P4;

   --  Missing post on Get for previous indexes on Insert

  package P5 is
      Max : constant := 100;
      type Index_Type is new Integer range 1 .. Max;
      subtype Ext_Index is Index_Type'Base range 0 .. Max;

      type Element_Type is private;

      type T is private with
        Aggregate => (Empty       => Empty,
                      Add_Unnamed => Append),
        Annotate => (GNATprove, Container_Aggregates, "Predefined_Sequences"); --@CONTAINER_AGGR_ANNOTATION:FAIL

      function Empty return T with
        Global => null,
        Import,
        Post => Last (Empty'Result) = First - 1;
      procedure Append (X : in out T; E : Element_Type) with
        Global => null,
        Always_Terminates,
        Pre => Last (X) < Max,
        Post => Last (X) = Last (X)'Old + 1
        and then Get (X, Last (X)) = E,
        Import;

      function Get (X : T; I : Index_Type) return Element_Type with
        Annotate => (GNATprove, Container_Aggregates, "Get"),
        Pre => I <= Last (X),
        Global => null,
        Import;

      function Last (X : T) return Ext_Index with
        Annotate => (GNATprove, Container_Aggregates, "Last"),
        Global => null,
        Import;

      function First return Index_Type with
        Annotate => (GNATprove, Container_Aggregates, "First"),
        Global => null,
        Import;

   private
      pragma SPARK_Mode (Off);
      type Element_Type is new Integer;
      type T is new Integer;
   end P5;

   --  Incorrect precondition on Empty

  package P6 is
      Max : constant := 100;
      type Index_Type is new Integer range 1 .. Max;
      subtype Ext_Index is Index_Type'Base range 0 .. Max;

      type Element_Type is private;

      type T is private with
        Aggregate => (Empty       => Empty,
                      Add_Unnamed => Append),
        Annotate => (GNATprove, Container_Aggregates, "Predefined_Sequences");

      function Pred return Boolean with
        Global => null,
        Import;

      function Empty return T with
        Global => null,
        Import,
        Pre => Pred,  --@PRECONDITION:FAIL
        Post => Last (Empty'Result) = First - 1;
      procedure Append (X : in out T; E : Element_Type) with
        Global => null,
        Always_Terminates,
        Pre => Last (X) < Max,
        Post => Last (X) = Last (X)'Old + 1
        and then Get (X, Last (X)) = E
        and then (for all I in First .. Last (X) - 1 =>
                    Get (X, I) = Get (X'Old, I)),
        Import;

      function Get (X : T; I : Index_Type) return Element_Type with
        Annotate => (GNATprove, Container_Aggregates, "Get"),
        Pre => I <= Last (X),
        Global => null,
        Import;

      function Last (X : T) return Ext_Index with
        Annotate => (GNATprove, Container_Aggregates, "Last"),
        Global => null,
        Import;

      function First return Index_Type with
        Annotate => (GNATprove, Container_Aggregates, "First"),
        Global => null,
        Import;

   private
      pragma SPARK_Mode (Off);
      type Element_Type is new Integer;
      type T is new Integer;
   end P6;

   --  Incorrect precondition on Insert

  package P7 is
      Max : constant := 100;
      type Index_Type is new Integer range 1 .. Max;
      subtype Ext_Index is Index_Type'Base range 0 .. Max;

      type Element_Type is private;

      type T is private with
        Aggregate => (Empty       => Empty,
                      Add_Unnamed => Append),
        Annotate => (GNATprove, Container_Aggregates, "Predefined_Sequences");

      function Pred (X : T; E : Element_Type) return Boolean with
        Global => null,
        Import;

      function Empty return T with
        Global => null,
        Import,
        Post => Last (Empty'Result) = First - 1;
      procedure Append (X : in out T; E : Element_Type) with
        Global => null,
        Always_Terminates,
        Pre => Last (X) < Max and then Pred (X, E), --@PRECONDITION:FAIL
        Post => Last (X) = Last (X)'Old + 1
        and then Get (X, Last (X)) = E
        and then (for all I in First .. Last (X) - 1 =>
                    Get (X, I) = Get (X'Old, I)),
        Import;

      function Get (X : T; I : Index_Type) return Element_Type with
        Annotate => (GNATprove, Container_Aggregates, "Get"),
        Pre => I <= Last (X),
        Global => null,
        Import;

      function Last (X : T) return Ext_Index with
        Annotate => (GNATprove, Container_Aggregates, "Last"),
        Global => null,
        Import;

      function First return Index_Type with
        Annotate => (GNATprove, Container_Aggregates, "First"),
        Global => null,
        Import;

   private
      pragma SPARK_Mode (Off);
      type Element_Type is new Integer;
      type T is new Integer;
   end P7;

   --  Missing Post on Capacity on Empty

   package P8 is
      type Index_Type is range 1 .. 100;
      subtype Ext_Index_Type is Index_Type'Base range 0 .. Index_Type'Last;
      type Element_Type is new Integer;

      Max_Capacity : constant Natural := Natural (Index_Type'Last);

      type T (Capacity : Natural) is private with
        Aggregate => (Empty       => Empty,
                      Add_Unnamed => Append),
        Annotate => (GNATprove, Container_Aggregates, "Predefined_Sequences"); --@CONTAINER_AGGR_ANNOTATION:FAIL

      function Empty (X : Natural) return T with
        Global => null,
        Import,
        Post => Last (Empty'Result) = 0;
      procedure Append (X : in out T; E : Element_Type) with
        Global => null,
        Pre  => Integer (Last (X)) < Capacity (X) and then Last (X) < 100,
        Post => Last (X) = Last (X'Old) + 1
        and then Get (X, Last (X)) = E
        and then (for all I in 1 .. Last (X) - 1 =>
                    Get (X, I) = Get (X'Old, I))
        and then Capacity (X) >= Capacity (X'Old),
        Always_Terminates,
        Import;

      function Capacity (X : T) return Natural with
        Global => null,
        Import,
        Annotate => (GNATprove, Container_Aggregates, "Capacity");

      function First return Ext_Index_Type is (1) with
        Annotate => (GNATprove, Container_Aggregates, "First");

      function Last (X : T) return Ext_Index_Type with
        Annotate => (GNATprove, Container_Aggregates, "Last");

      function Get (X : T; I : Index_Type) return Element_Type with
        Pre => I <= Last (X),
        Annotate => (GNATprove, Container_Aggregates, "Get");

   private
      type T_Content is array (Positive range <>) of Element_Type with
        Relaxed_Initialization;

      type T (Capacity : Natural) is record
         Content : T_Content (1 .. Capacity);
         Top     : Natural;
      end record with
        Ghost_Predicate => Capacity <= Max_Capacity
        and then Top <= Capacity
        and then (for all I in 1 .. Top => Content (I)'Initialized);

      function Last (X : T) return Ext_Index_Type is (Ext_Index_Type (X.Top));

      function Get (X : T; I : Index_Type) return Element_Type is
        (X.Content (Positive (I)));
   end P8;

   --  Missing Post on Capacity on Append

   package P9 is
      type Index_Type is range 1 .. 100;
      subtype Ext_Index_Type is Index_Type'Base range 0 .. Index_Type'Last;
      type Element_Type is new Integer;

      Max_Capacity : constant Natural := Natural (Index_Type'Last);

      type T (Capacity : Natural) is private with
        Aggregate => (Empty       => Empty,
                      Add_Unnamed => Append),
        Annotate => (GNATprove, Container_Aggregates, "Predefined_Sequences"); --@CONTAINER_AGGR_ANNOTATION:FAIL

      function Empty (X : Natural) return T with
        Global => null,
        Import,
        Post => Last (Empty'Result) = 0
        and then (if X <= Max_Capacity then Capacity (Empty'Result) = X);
      procedure Append (X : in out T; E : Element_Type) with
        Global => null,
        Pre  => Integer (Last (X)) < Capacity (X) and then Last (X) < 100,
        Post => Last (X) = Last (X'Old) + 1
        and then Get (X, Last (X)) = E
        and then (for all I in 1 .. Last (X) - 1 =>
                    Get (X, I) = Get (X'Old, I)),
        Always_Terminates,
        Import;

      function Capacity (X : T) return Natural with
        Global => null,
        Import,
        Annotate => (GNATprove, Container_Aggregates, "Capacity");

      function First return Ext_Index_Type is (1) with
        Annotate => (GNATprove, Container_Aggregates, "First");

      function Last (X : T) return Ext_Index_Type with
        Annotate => (GNATprove, Container_Aggregates, "Last");

      function Get (X : T; I : Index_Type) return Element_Type with
        Pre => I <= Last (X),
        Annotate => (GNATprove, Container_Aggregates, "Get");

   private
      type T_Content is array (Positive range <>) of Element_Type with
        Relaxed_Initialization;

      type T (Capacity : Natural) is record
         Content : T_Content (1 .. Capacity);
         Top     : Natural;
      end record with
        Ghost_Predicate => Capacity <= Max_Capacity
        and then Top <= Capacity
        and then (for all I in 1 .. Top => Content (I)'Initialized);

      function Last (X : T) return Ext_Index_Type is (Ext_Index_Type (X.Top));

      function Get (X : T; I : Index_Type) return Element_Type is
        (X.Content (Positive (I)));
   end P9;

   --  Correct posts on Capacity

   package P10 is
      type Index_Type is range 1 .. 100;
      subtype Ext_Index_Type is Index_Type'Base range 0 .. Index_Type'Last;
      type Element_Type is new Integer;

      Max_Capacity : constant Natural := Natural (Index_Type'Last);

      type T (Capacity : Natural) is private with
        Aggregate => (Empty       => Empty,
                      Add_Unnamed => Append),
        Annotate => (GNATprove, Container_Aggregates, "Predefined_Sequences"); --@CONTAINER_AGGR_ANNOTATION:PASS

      function Empty (X : Natural) return T with
        Global => null,
        Import,
        Post => Last (Empty'Result) = 0
        and then (if X <= Max_Capacity then Capacity (Empty'Result) = X);
      procedure Append (X : in out T; E : Element_Type) with
        Global => null,
        Pre  => Integer (Last (X)) < Capacity (X) and then Last (X) < 100,
        Post => Last (X) = Last (X'Old) + 1
        and then Get (X, Last (X)) = E
        and then (for all I in 1 .. Last (X) - 1 =>
                    Get (X, I) = Get (X'Old, I))
        and then Capacity (X) >= Capacity (X'Old),
        Always_Terminates,
        Import;

      function Capacity (X : T) return Natural with
        Global => null,
        Import,
        Annotate => (GNATprove, Container_Aggregates, "Capacity");

      function First return Ext_Index_Type is (1) with
        Annotate => (GNATprove, Container_Aggregates, "First");

      function Last (X : T) return Ext_Index_Type with
        Annotate => (GNATprove, Container_Aggregates, "Last");

      function Get (X : T; I : Index_Type) return Element_Type with
        Pre => I <= Last (X),
        Annotate => (GNATprove, Container_Aggregates, "Get");

   private
      type T_Content is array (Positive range <>) of Element_Type with
        Relaxed_Initialization;

      type T (Capacity : Natural) is record
         Content : T_Content (1 .. Capacity);
         Top     : Natural;
      end record with
        Ghost_Predicate => Capacity <= Max_Capacity
        and then Top <= Capacity
        and then (for all I in 1 .. Top => Content (I)'Initialized);

      function Last (X : T) return Ext_Index_Type is (Ext_Index_Type (X.Top));

      function Get (X : T; I : Index_Type) return Element_Type is
        (X.Content (Positive (I)));
   end P10;

   --  No post needed on global Capacity

   package P11 is
      type Index_Type is range 1 .. 100;
      subtype Ext_Index_Type is Index_Type'Base range 0 .. Index_Type'Last;
      type Element_Type is new Integer;

      Max_Capacity : constant Natural := Natural (Index_Type'Last);

      type T is private with
        Aggregate => (Empty       => Empty,
                      Add_Unnamed => Append),
        Annotate => (GNATprove, Container_Aggregates, "Predefined_Sequences"); --@CONTAINER_AGGR_ANNOTATION:PASS

      function Empty return T with
        Global => null,
        Import,
        Post => Last (Empty'Result) = 0;
      procedure Append (X : in out T; E : Element_Type) with
        Global => null,
        Pre  => Integer (Last (X)) < Capacity and then Last (X) < 100,
        Post => Last (X) = Last (X'Old) + 1
        and then Get (X, Last (X)) = E
        and then (for all I in 1 .. Last (X) - 1 =>
                    Get (X, I) = Get (X'Old, I)),
        Always_Terminates,
        Import;

      function Capacity return Natural with
        Global => null,
        Import,
        Annotate => (GNATprove, Container_Aggregates, "Capacity");

      function First return Ext_Index_Type is (1) with
        Annotate => (GNATprove, Container_Aggregates, "First");

      function Last (X : T) return Ext_Index_Type with
        Annotate => (GNATprove, Container_Aggregates, "Last");

      function Get (X : T; I : Index_Type) return Element_Type with
        Pre => I <= Last (X),
        Annotate => (GNATprove, Container_Aggregates, "Get");

   private
      type T_Content is array (Positive range 1 .. Capacity) of Element_Type with
        Relaxed_Initialization;

      type T is record
         Content : T_Content;
         Top     : Natural;
      end record with
        Ghost_Predicate => Top <= Max_Capacity
        and then Top <= Capacity
        and then (for all I in 1 .. Top => Content (I)'Initialized);

      function Last (X : T) return Ext_Index_Type is (Ext_Index_Type (X.Top));

      function Get (X : T; I : Index_Type) return Element_Type is
        (X.Content (Positive (I)));
   end P11;
begin
   null;
end;
