procedure Test_Illegal_Last with SPARK_Mode is

   --  Incorrect Last, no parameters

   package P1 is
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

      function Last return Ext_Index with
        Global => null,
        Import,
        Annotate => (GNATprove, Container_Aggregates, "Last");

      function Get (X : T; I : Index_Type) return Element_Type with
        Annotate => (GNATprove, Container_Aggregates, "Get");

      function First return Index_Type is (1) with
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
   end P1;

   --  Incorrect Last, bad first parameter

   package P2 is
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

      function Last (X : Ext_Index) return Ext_Index with
        Global => null,
        Import,
        Annotate => (GNATprove, Container_Aggregates, "Last");

      function Get (X : T; I : Index_Type) return Element_Type with
        Annotate => (GNATprove, Container_Aggregates, "Get");

      function First return Index_Type is (1) with
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
   end P2;

   --  Incorrect Last, bad number of parameters

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

      function Last (X : T; I : Index_Type) return Ext_Index with
        Global => null,
        Import,
        Annotate => (GNATprove, Container_Aggregates, "Last");

      function Get (X : T; I : Index_Type) return Element_Type with
        Annotate => (GNATprove, Container_Aggregates, "Get");

      function First return Index_Type is (1) with
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
   end P3;

   --  Incorrect Last, noninteger return type

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

      function Last (X : T) return T with
        Global => null,
        Import,
        Annotate => (GNATprove, Container_Aggregates, "Last");

      function Get (X : T; I : Index_Type) return Element_Type with
        Annotate => (GNATprove, Container_Aggregates, "Get");

      function First return Index_Type is (1) with
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
   end P4;

   --  Incorrect Last, incompatible return type

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

      function Get (X : T; I : Index_Type) return Element_Type with
        Annotate => (GNATprove, Container_Aggregates, "Get");

      function First return Index_Type is (1) with
        Annotate => (GNATprove, Container_Aggregates, "First");

      function Last (X : T) return Integer with
        Global => null,
        Import,
        Annotate => (GNATprove, Container_Aggregates, "Last");

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
   end P5;

   --  Incorrect Last, duplicate function

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
        Global => null,
        Import,
        Annotate => (GNATprove, Container_Aggregates, "Last");

      function Last2 (X : T) return Ext_Index with
        Global => null,
        Import,
        Annotate => (GNATprove, Container_Aggregates, "Last");

      function Get (X : T; I : Index_Type) return Element_Type with
        Annotate => (GNATprove, Container_Aggregates, "Get");

      function First return Index_Type is (1) with
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
   end P6;

   --  Incorrect Last, bad location

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

      package Nested is
         function Last (X : T) return Ext_Index with
           Global => null,
           Import,
           Annotate => (GNATprove, Container_Aggregates, "Last");
      end Nested;

      function Get (X : T; I : Index_Type) return Element_Type with
        Annotate => (GNATprove, Container_Aggregates, "Get");

      function First return Index_Type is (1) with
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
   end P7;

   --  Incorrect Last, bad location of annotate

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

      function Last (X : T) return Ext_Index with
        Global => null,
        Import;

      function Get (X : T; I : Index_Type) return Element_Type with
        Annotate => (GNATprove, Container_Aggregates, "Get");

      function First return Index_Type is (1) with
        Annotate => (GNATprove, Container_Aggregates, "First");

     pragma Annotate (GNATprove, Container_Aggregates, "Last", Last);

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
   end P8;

   --  Incorrect Last, function with side effects

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
        Side_Effects,
        Global => null,
        Import,
        Annotate => (GNATprove, Container_Aggregates, "Last");

      function Get (X : T; I : Index_Type) return Element_Type with
        Annotate => (GNATprove, Container_Aggregates, "Get");

      function First return Index_Type is (1) with
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
   end P9;

   --  Incorrect Last, volatile function

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
        Volatile_Function,
        Global => null,
        Import,
        Annotate => (GNATprove, Container_Aggregates, "Last");

      function Get (X : T; I : Index_Type) return Element_Type with
        Annotate => (GNATprove, Container_Aggregates, "Get");

      function First return Index_Type is (1) with
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
   end P10;

   --  Incorrect Last, SPARK_Mode => Off

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
        SPARK_Mode => Off,
        Global => null,
        Import,
        Annotate => (GNATprove, Container_Aggregates, "Last");

      function Get (X : T; I : Index_Type) return Element_Type with
        Annotate => (GNATprove, Container_Aggregates, "Get");

      function First return Index_Type is (1) with
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
   end P11;

   --  Incorrect Last, global access

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
        Annotate => (GNATprove, Container_Aggregates, "Get");

      function First return Index_Type is (1) with
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

      V : Index_Type;

      function Last (X : T) return Ext_Index is (V);
   end P12;

begin
   null;
end Test_Illegal_Last;
