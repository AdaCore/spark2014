procedure Test_Illegal_Seqs_Get with SPARK_Mode is

   --  Incorrect Get, no parameters

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

      function Get return Element_Type with
        Global => null,
        Import,
        Annotate => (GNATprove, Container_Aggregates, "Get");

      function Last (X : T) return Ext_Index with
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

      function Last (X : T) return Ext_Index is (X.Top);
   end P1;

   --  Incorrect Get, bad first parameters

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

      function Get (X : Natural; I : Index_Type) return Element_Type with
        Global => null,
        Import,
        Annotate => (GNATprove, Container_Aggregates, "Get");

      function Last (X : T) return Ext_Index with
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

      function Last (X : T) return Ext_Index is (X.Top);
   end P2;

   --  Incorrect Get, bad number of parameters

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

      function Get (X : T) return Element_Type with
        Global => null,
        Import,
        Annotate => (GNATprove, Container_Aggregates, "Get");

      function Last (X : T) return Ext_Index with
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

      function Last (X : T) return Ext_Index is (X.Top);
   end P3;

   --  Incorrect Get, non integer second parameter

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

      function Get (X : T; I : Boolean) return Element_Type with
        Global => null,
        Import,
        Annotate => (GNATprove, Container_Aggregates, "Get");

      function Last (X : T) return Ext_Index with
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

      function Last (X : T) return Ext_Index is (X.Top);
   end P4;

   --  Incorrect Get, incompatible second parameter

   package P4_bis is
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

      function Get (X : T; I : Positive) return Element_Type with
        Global => null,
        Import,
        Annotate => (GNATprove, Container_Aggregates, "Get");

   private
      type T_Content is array (Index_Type) of Element_Type with
        Relaxed_Initialization;
      type T is record
         Content : T_Content;
         Top     : Ext_Index;
      end record with
        Ghost_Predicate =>
          (for all I in 1 .. Top => Content (I)'Initialized);

      function Last (X : T) return Ext_Index is (X.Top);
   end P4_bis;

   --  Incorrect Get, bad return type

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

      function Get (X : T; I : Index_Type) return Boolean with
        Global => null,
        Import,
        Annotate => (GNATprove, Container_Aggregates, "Get");

      function Last (X : T) return Ext_Index with
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

      function Last (X : T) return Ext_Index is (X.Top);
   end P5;

   --  Incorrect Get, duplicate function

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

      function Get (X : T; I : Index_Type) return Element_Type with
        Global => null,
        Import,
        Annotate => (GNATprove, Container_Aggregates, "Get");

      function Get2 (X : T; I : Index_Type) return Element_Type with
        Global => null,
        Import,
        Annotate => (GNATprove, Container_Aggregates, "Get");

      function Last (X : T) return Ext_Index with
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

      function Last (X : T) return Ext_Index is (X.Top);
   end P6;

   --  Incorrect Get, bad location

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
         function Get (X : T; I : Index_Type) return Element_Type with
           Global => null,
           Import,
           Annotate => (GNATprove, Container_Aggregates, "Get");
      end Nested;

      function Last (X : T) return Ext_Index with
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

      function Last (X : T) return Ext_Index is (X.Top);
   end P7;

   --  Incorrect Get, bad location of annotate

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

      function Get (X : T; I : Index_Type) return Element_Type with
        Global => null,
        Import;

      function Last (X : T) return Ext_Index with
        Annotate => (GNATprove, Container_Aggregates, "Last");

      pragma Annotate (GNATprove, Container_Aggregates, "Get", Get);

   private
      type T_Content is array (Index_Type) of Element_Type with
        Relaxed_Initialization;
      type T is record
         Content : T_Content;
         Top     : Ext_Index;
      end record with
        Ghost_Predicate =>
          (for all I in 1 .. Top => Content (I)'Initialized);

      function Last (X : T) return Ext_Index is (X.Top);
   end P8;

   --  Incorrect Get, function with side effects

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

      function Get (X : T; I : Index_Type) return Element_Type with
        Side_Effects,
        Global => null,
        Import,
        Annotate => (GNATprove, Container_Aggregates, "Get");

      function Last (X : T) return Ext_Index with
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

      function Last (X : T) return Ext_Index is (X.Top);
   end P9;

   --  Incorrect Get, volatile function

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

      function Get (X : T; I : Index_Type) return Element_Type with
        Volatile_Function,
        Global => null,
        Import,
        Annotate => (GNATprove, Container_Aggregates, "Get");

      function Last (X : T) return Ext_Index with
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

      function Last (X : T) return Ext_Index is (X.Top);
   end P10;

   --  Incorrect Get, SPARK_Mode => Off

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

      function Get (X : T; I : Index_Type) return Element_Type with
        SPARK_Mode => Off,
        Global => null,
        Import,
        Annotate => (GNATprove, Container_Aggregates, "Get");

      function Last (X : T) return Ext_Index with
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

      function Last (X : T) return Ext_Index is (X.Top);
   end P11;

   --  Incorrect Get, global access

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

      function Get (X : T; I : Index_Type) return Element_Type with
        Annotate => (GNATprove, Container_Aggregates, "Get");

      function Last (X : T) return Ext_Index with
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

      function Last (X : T) return Ext_Index is (X.Top);
      B : Element_Type;
      function Get (X : T; I : Index_Type) return Element_Type is
        (B + X.Content (I));
   end P12;

begin
   null;
end Test_Illegal_Seqs_Get;
