procedure Test_Illegal_Seqs with SPARK_Mode is

   --  Sequence aggregate shall have an Add_Unnamed procedure

   package P1 is
      type Index_Type is new Integer range 1 .. 100;
      subtype Ext_Index is Index_Type'Base range 0 .. 100;

      type Element_Type is new Integer;

      type T is private with
        Aggregate => (Empty          => Empty,
                      New_Indexed    => New_Vector,
                      Assign_Indexed => Assign_Element),
        Annotate => (GNATprove, Container_Aggregates, "Predefined_Sequences");

      function All_Init (X : T; Up : Ext_Index) return Boolean with Ghost;

      function Empty return T with
        Import,
        Global => null;

      function New_Vector (First, Last : Index_Type) return T with
        Import,
        Global => null,
        Pre => First = Index_Type'First;

      procedure Assign_Element (V     : in out T;
                                Index : Index_Type;
                                Item  : Element_Type)
      with
        Global => null,
        Always_Terminates,
        Import,
        Pre => All_Init (V, Index - 1),
        Post => All_Init (V, Index);

   private
      type T_Content is array (Index_Type) of Element_Type with
        Relaxed_Initialization;
      type T is record
         Content : T_Content;
         Top     : Ext_Index;
      end record;

      function All_Init (X : T; Up : Ext_Index) return Boolean is
        (for all I in 1 .. Up => X.Content (I)'Initialized);
   end P1;

   --  Sequence aggregate shall have a Get function

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

      function Last (X : T) return Ext_Index with
        Annotate => (GNATprove, Container_Aggregates, "Last");

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

      function Last (X : T) return Ext_Index is (X.Top);
   end P2;

   --  Sequence aggregate shall have an Last function

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

   --  Sequence aggregate shall have a first function

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

      function Get (X : T; I : Index_Type) return Element_Type with
        Annotate => (GNATprove, Container_Aggregates, "Get"),
        Pre => I <= Last (X);

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

      function Get (X : T; I : Index_Type) return Element_Type is
        (X.Content (I));

      function Last (X : T) return Ext_Index is (X.Top);
   end P4;

   --  Sequence aggregate with a get, a last, and a first function

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
        Annotate => (GNATprove, Container_Aggregates, "Get"),
        Pre => I <= Last (X);

      function Last (X : T) return Ext_Index with
        Annotate => (GNATprove, Container_Aggregates, "Last");

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

      function Last (X : T) return Ext_Index is (X.Top);
   end P5;

   --  Other primitives are not expected

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
        Annotate => (GNATprove, Container_Aggregates, "Get"),
        Pre => I <= Last (X);

      function Last (X : T) return Ext_Index with
        Annotate => (GNATprove, Container_Aggregates, "Last");

      function First return Index_Type is (1) with
        Annotate => (GNATprove, Container_Aggregates, "First");

      function Length (X : T) return Natural with
        Annotate => (GNATprove, Container_Aggregates, "Length");

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

      function Length (X : T) return Natural is (Natural (X.Top));
   end P6;

begin
   null;
end Test_Illegal_Seqs;
