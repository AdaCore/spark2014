procedure Test_Illegal_First with SPARK_Mode is

   --  Incorrect First, bad number of parameters

   package P3 is
      type Index_Type is new Integer range 1 .. 100;
      subtype Ext_Index is Index_Type'Base range 0 .. 100;

      type Element_Type is new Integer;

      type T is private with
        Aggregate => (Empty       => Empty,
                      Add_Unnamed => Append),
        Annotate => (GNATprove, Container_Aggregates, "Predefined_Sequences");

      function Empty return T with
        Import,
        Global => null;
      procedure Append (X : in out T; E : Element_Type) with
        Global => null,
        Always_Terminates,
        Import;

      function Last (X : T) return Ext_Index with
        Annotate => (GNATprove, Container_Aggregates, "Last");

      function Get (X : T; I : Index_Type) return Element_Type with
        Pre => I <= Last (X),
        Annotate => (GNATprove, Container_Aggregates, "Get");

      function First (X : T) return Index_Type with
        Global => null,
        Import,
        Annotate => (GNATprove, Container_Aggregates, "First");

   private
      type T_Content is array (Index_Type) of Element_Type with
        Relaxed_Initialization;
      type T is record
         Content : T_Content;
         Top     : Ext_Index;
      end record with
        Ghost_Predicate =>
          (for all I in 1 .. Top => Content (I)'Initialized);

      function Get (X : T; I : Index_Type) return Element_Type is
        (X.Content (I));

      function Last (X : T) return Ext_Index is (X.Top);
   end P3;

   --  Incorrect First, noninteger return type

   package P4 is
      type Index_Type is new Integer range 1 .. 100;
      subtype Ext_Index is Index_Type'Base range 0 .. 100;

      type Element_Type is new Integer;

      type T is private with
        Aggregate => (Empty       => Empty,
                      Add_Unnamed => Append),
        Annotate => (GNATprove, Container_Aggregates, "Predefined_Sequences");

      function Empty return T with
        Import,
        Global => null;
      procedure Append (X : in out T; E : Element_Type) with
        Global => null,
        Always_Terminates,
        Import;

      function Last (X : T) return Ext_Index with
        Annotate => (GNATprove, Container_Aggregates, "Last");

      function Get (X : T; I : Index_Type) return Element_Type with
        Pre => I <= Last (X),
        Annotate => (GNATprove, Container_Aggregates, "Get");

      function First return Boolean with
        Global => null,
        Import,
        Annotate => (GNATprove, Container_Aggregates, "First");

   private
      type T_Content is array (Index_Type) of Element_Type with
        Relaxed_Initialization;
      type T is record
         Content : T_Content;
         Top     : Ext_Index;
      end record with
        Ghost_Predicate =>
          (for all I in 1 .. Top => Content (I)'Initialized);

      function Get (X : T; I : Index_Type) return Element_Type is
        (X.Content (I));

      function Last (X : T) return Ext_Index is (X.Top);
   end P4;

   --  Incorrect First, incompatible return type
   --  ??? Here there is no specific complaint, First is just not found. It is
   --  because First does not take the container as parameter so it is
   --  difficult to know what the expected index type would be.

   package P5 is
      type Index_Type is new Integer range 1 .. 100;
      subtype Ext_Index is Index_Type'Base range 0 .. 100;

      type Element_Type is new Integer;

      type T is private with
        Aggregate => (Empty       => Empty,
                      Add_Unnamed => Append),
        Annotate => (GNATprove, Container_Aggregates, "Predefined_Sequences");

      function Empty return T with
        Import,
        Global => null;
      procedure Append (X : in out T; E : Element_Type) with
        Global => null,
        Always_Terminates,
        Import;

      function Last (X : T) return Ext_Index with
        Annotate => (GNATprove, Container_Aggregates, "Last");

      function Get (X : T; I : Index_Type) return Element_Type with
        Pre => I <= Last (X),
        Annotate => (GNATprove, Container_Aggregates, "Get");

      function First return Integer with
        Global => null,
        Import,
        Annotate => (GNATprove, Container_Aggregates, "First");

   private
      type T_Content is array (Index_Type) of Element_Type with
        Relaxed_Initialization;
      type T is record
         Content : T_Content;
         Top     : Ext_Index;
      end record with
        Ghost_Predicate =>
          (for all I in 1 .. Top => Content (I)'Initialized);

      function Get (X : T; I : Index_Type) return Element_Type is
        (X.Content (I));

      function Last (X : T) return Ext_Index is (X.Top);
   end P5;

   --  Incorrect First, duplicate function

   package P6 is
      type Index_Type is new Integer range 1 .. 100;
      subtype Ext_Index is Index_Type'Base range 0 .. 100;

      type Element_Type is new Integer;

      type T is private with
        Aggregate => (Empty       => Empty,
                      Add_Unnamed => Append),
        Annotate => (GNATprove, Container_Aggregates, "Predefined_Sequences");

      function Empty return T with
        Import,
        Global => null;
      procedure Append (X : in out T; E : Element_Type) with
        Global => null,
        Always_Terminates,
        Import;

      function Last (X : T) return Ext_Index with
        Annotate => (GNATprove, Container_Aggregates, "Last");

      function Get (X : T; I : Index_Type) return Element_Type with
        Pre => I <= Last (X),
        Annotate => (GNATprove, Container_Aggregates, "Get");

      function First return Index_Type with
        Global => null,
        Import,
        Annotate => (GNATprove, Container_Aggregates, "First");

      function First2 return Index_Type with
        Global => null,
        Import,
        Annotate => (GNATprove, Container_Aggregates, "First");

   private
      type T_Content is array (Index_Type) of Element_Type with
        Relaxed_Initialization;
      type T is record
         Content : T_Content;
         Top     : Ext_Index;
      end record with
        Ghost_Predicate =>
          (for all I in 1 .. Top => Content (I)'Initialized);

      function Get (X : T; I : Index_Type) return Element_Type is
        (X.Content (I));

      function Last (X : T) return Ext_Index is (X.Top);
   end P6;

   --  Incorrect First, bad location
   --  ??? Here there is no specific complaint, First is just not found. It is
   --  because First does not take the container as parameter so it is
   --  difficult to be sure that it is not in the right scope.

   package P7 is
      type Index_Type is new Integer range 1 .. 100;
      subtype Ext_Index is Index_Type'Base range 0 .. 100;

      type Element_Type is new Integer;

      type T is private with
        Aggregate => (Empty       => Empty,
                      Add_Unnamed => Append),
        Annotate => (GNATprove, Container_Aggregates, "Predefined_Sequences");

      function Empty return T with
        Import,
        Global => null;
      procedure Append (X : in out T; E : Element_Type) with
        Global => null,
        Always_Terminates,
        Import;

      function Last (X : T) return Ext_Index with
        Annotate => (GNATprove, Container_Aggregates, "Last");

      function Get (X : T; I : Index_Type) return Element_Type with
        Pre => I <= Last (X),
        Annotate => (GNATprove, Container_Aggregates, "Get");

      package Nested is
         function First return Index_Type with
           Global => null,
           Import,
           Annotate => (GNATprove, Container_Aggregates, "First");
      end Nested;

   private
      type T_Content is array (Index_Type) of Element_Type with
        Relaxed_Initialization;
      type T is record
         Content : T_Content;
         Top     : Ext_Index;
      end record with
        Ghost_Predicate =>
          (for all I in 1 .. Top => Content (I)'Initialized);

      function Get (X : T; I : Index_Type) return Element_Type is
        (X.Content (I));

      function Last (X : T) return Ext_Index is (X.Top);
   end P7;

   --  Incorrect First, bad location of annotate

   package P8 is
      type Index_Type is new Integer range 1 .. 100;
      subtype Ext_Index is Index_Type'Base range 0 .. 100;

      type Element_Type is new Integer;

      type T is private with
        Aggregate => (Empty       => Empty,
                      Add_Unnamed => Append),
        Annotate => (GNATprove, Container_Aggregates, "Predefined_Sequences");

      function Empty return T with
        Import,
        Global => null;
      procedure Append (X : in out T; E : Element_Type) with
        Global => null,
        Always_Terminates,
        Import;

      function First return Index_Type with
        Global => null,
        Import;

      function Last (X : T) return Ext_Index with
        Annotate => (GNATprove, Container_Aggregates, "Last");

      function Get (X : T; I : Index_Type) return Element_Type with
        Pre => I <= Last (X),
        Annotate => (GNATprove, Container_Aggregates, "Get");

      pragma Annotate (GNATprove, Container_Aggregates, "First", First);

   private
      type T_Content is array (Index_Type) of Element_Type with
        Relaxed_Initialization;
      type T is record
         Content : T_Content;
         Top     : Ext_Index;
      end record with
        Ghost_Predicate =>
          (for all I in 1 .. Top => Content (I)'Initialized);

      function Get (X : T; I : Index_Type) return Element_Type is
        (X.Content (I));

      function Last (X : T) return Ext_Index is (X.Top);
   end P8;

   --  Incorrect First, function with side effects

   package P9 is
      type Index_Type is new Integer range 1 .. 100;
      subtype Ext_Index is Index_Type'Base range 0 .. 100;

      type Element_Type is new Integer;

      type T is private with
        Aggregate => (Empty       => Empty,
                      Add_Unnamed => Append),
        Annotate => (GNATprove, Container_Aggregates, "Predefined_Sequences");

      function Empty return T with
        Import,
        Global => null;
      procedure Append (X : in out T; E : Element_Type) with
        Global => null,
        Always_Terminates,
        Import;

      function Last (X : T) return Ext_Index with
        Annotate => (GNATprove, Container_Aggregates, "Last");

      function Get (X : T; I : Index_Type) return Element_Type with
        Pre => I <= Last (X),
        Annotate => (GNATprove, Container_Aggregates, "Get");

      function First return Index_Type with
        Side_Effects,
        Global => null,
        Import,
        Annotate => (GNATprove, Container_Aggregates, "First");

   private
      type T_Content is array (Index_Type) of Element_Type with
        Relaxed_Initialization;
      type T is record
         Content : T_Content;
         Top     : Ext_Index;
      end record with
        Ghost_Predicate =>
          (for all I in 1 .. Top => Content (I)'Initialized);

      function Get (X : T; I : Index_Type) return Element_Type is
        (X.Content (I));

      function Last (X : T) return Ext_Index is (X.Top);
   end P9;

   --  Incorrect First, volatile function

   package P10 is
      type Index_Type is new Integer range 1 .. 100;
      subtype Ext_Index is Index_Type'Base range 0 .. 100;

      type Element_Type is new Integer;

      type T is private with
        Aggregate => (Empty       => Empty,
                      Add_Unnamed => Append),
        Annotate => (GNATprove, Container_Aggregates, "Predefined_Sequences");

      function Empty return T with
        Import,
        Global => null;
      procedure Append (X : in out T; E : Element_Type) with
        Global => null,
        Always_Terminates,
        Import;

      function Last (X : T) return Ext_Index with
        Annotate => (GNATprove, Container_Aggregates, "Last");

      function Get (X : T; I : Index_Type) return Element_Type with
        Pre => I <= Last (X),
        Annotate => (GNATprove, Container_Aggregates, "Get");

      function First return Index_Type with
        Volatile_Function,
        Global => null,
        Import,
        Annotate => (GNATprove, Container_Aggregates, "First");

   private
      type T_Content is array (Index_Type) of Element_Type with
        Relaxed_Initialization;
      type T is record
         Content : T_Content;
         Top     : Ext_Index;
      end record with
        Ghost_Predicate =>
          (for all I in 1 .. Top => Content (I)'Initialized);

      function Get (X : T; I : Index_Type) return Element_Type is
        (X.Content (I));

      function Last (X : T) return Ext_Index is (X.Top);
   end P10;

   --  Incorrect First, SPARK_Mode => Off
   --  ??? Here there is no specific complaint, First is just not found. It
   --  is because First does not take the container as parameter so it is
   --  difficult to know whether it is in SPARK.

   package P11 is
      type Index_Type is new Integer range 1 .. 100;
      subtype Ext_Index is Index_Type'Base range 0 .. 100;

      type Element_Type is new Integer;

      type T is private with
        Aggregate => (Empty       => Empty,
                      Add_Unnamed => Append),
        Annotate => (GNATprove, Container_Aggregates, "Predefined_Sequences");

      function Empty return T with
        Import,
        Global => null;
      procedure Append (X : in out T; E : Element_Type) with
        Global => null,
        Always_Terminates,
        Import;

      function Last (X : T) return Ext_Index with
        Annotate => (GNATprove, Container_Aggregates, "Last");

      function Get (X : T; I : Index_Type) return Element_Type with
        Pre => I <= Last (X),
        Annotate => (GNATprove, Container_Aggregates, "Get");

      function First return Index_Type with
        SPARK_Mode => Off,
        Global => null,
        Import,
        Annotate => (GNATprove, Container_Aggregates, "First");

   private
      type T_Content is array (Index_Type) of Element_Type with
        Relaxed_Initialization;
      type T is record
         Content : T_Content;
         Top     : Ext_Index;
      end record with
        Ghost_Predicate =>
          (for all I in 1 .. Top => Content (I)'Initialized);

      function Get (X : T; I : Index_Type) return Element_Type is
        (X.Content (I));

      function Last (X : T) return Ext_Index is (X.Top);
   end P11;

   --  Incorrect First, global access

   package P12 is
      type Index_Type is new Integer range 1 .. 100;
      subtype Ext_Index is Index_Type'Base range 0 .. 100;

      type Element_Type is new Integer;

      type T is private with
        Aggregate => (Empty       => Empty,
                      Add_Unnamed => Append),
        Annotate => (GNATprove, Container_Aggregates, "Predefined_Sequences");

      function Empty return T with
        Import,
        Global => null;
      procedure Append (X : in out T; E : Element_Type) with
        Global => null,
        Always_Terminates,
        Import;

      function Last (X : T) return Ext_Index with
        Annotate => (GNATprove, Container_Aggregates, "Last");

      function Get (X : T; I : Index_Type) return Element_Type with
        Pre => I <= Last (X),
        Annotate => (GNATprove, Container_Aggregates, "Get");

      X : Index_Type;

      function First return Index_Type is (X) with
        Annotate => (GNATprove, Container_Aggregates, "First");

   private
      type T_Content is array (Index_Type) of Element_Type with
        Relaxed_Initialization;
      type T is record
         Content : T_Content;
         Top     : Ext_Index;
      end record with
        Ghost_Predicate =>
          (for all I in 1 .. Top => Content (I)'Initialized);

      function Get (X : T; I : Index_Type) return Element_Type is
        (X.Content (I));

      function Last (X : T) return Ext_Index is (X.Top);
   end P12;

begin
   null;
end Test_Illegal_First;
