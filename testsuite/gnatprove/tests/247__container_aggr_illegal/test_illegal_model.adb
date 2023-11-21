procedure Test_Illegal_Model with SPARK_Mode is

   type Index_Type is new Integer range 1 .. 100;
   subtype Ext_Index is Index_Type'Base range 0 .. 100;

   type Element_Type is new Integer;
   type Key_Type is range 1 .. 100;

   package Seqs is
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
   end Seqs;

   package Maps is
      type T is private with
        Aggregate => (Empty       => Empty,
                      Add_Named => Insert),
        Annotate => (GNATprove, Container_Aggregates, "Predefined_Maps");

      function Empty return T;
      procedure Insert (X : in out T; K : Key_Type; E : Element_Type) with
        Global => null,
        Pre => not Has_Key (X, K),
        Always_Terminates,
        Import;

      function Has_Key (X : T; K : Key_Type) return Boolean with
        Annotate => (GNATprove, Container_Aggregates, "Has_Key");

      function Get (X : T; K : Key_Type) return Element_Type with
        Pre => Has_Key (X, K),
        Annotate => (GNATprove, Container_Aggregates, "Get");

      function Eq_Key (X, Y : Key_Type) return Boolean is (X = Y) with
        Annotate => (GNATprove, Container_Aggregates, "Equivalent_Keys");

      type Length_Type is range 0 .. 100;

      function Length (X : T) return Length_Type with
        Annotate => (GNATprove, Container_Aggregates, "Length");

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

      function Empty return T is
        (null);

      function Has_Key (X : T; K : Key_Type) return Boolean is
        (if X = null then False else K = X.P.K or else Has_Key (X.N, K));

      function Get (X : T; K : Key_Type) return Element_Type is
        (if K = X.P.K then X.P.E else Get (X.N, K));

      function Length (X : T) return Length_Type is
        (if X = null then 0 else Length (X.N) + 1);
   end Maps;

   --  Incorrect Model, no parameters

   package P1 is
      type T is private with
        Aggregate => (Empty       => Empty,
                      Add_Unnamed => Append),
        Annotate => (GNATprove, Container_Aggregates, "From_Model");

      function Empty return T with
        Import,
        Global => null;
      procedure Append (X : in out T; E : Element_Type) with
        Global => null,
        Always_Terminates,
        Import;

      function Model return Seqs.T with
        Global => null,
        Import,
        Annotate => (GNATprove, Container_Aggregates, "Model");

   private
      type T_Content is array (Index_Type) of Element_Type with
        Relaxed_Initialization;
      type T is record
         Content : T_Content;
         Top     : Ext_Index;
      end record with
        Ghost_Predicate =>
          (for all I in 1 .. Top => Content (I)'Initialized);
   end P1;

   --  Incorrect Model, bad first parameter

   package P2 is
      type T is private with
        Aggregate => (Empty       => Empty,
                      Add_Unnamed => Append),
        Annotate => (GNATprove, Container_Aggregates, "From_Model");

      function Empty return T with
        Import,
        Global => null;
      procedure Append (X : in out T; E : Element_Type) with
        Global => null,
        Always_Terminates,
        Import;

      function Model (X : Integer) return Seqs.T with
        Global => null,
        Import,
        Annotate => (GNATprove, Container_Aggregates, "Model");

   private
      type T_Content is array (Index_Type) of Element_Type with
        Relaxed_Initialization;
      type T is record
         Content : T_Content;
         Top     : Ext_Index;
      end record with
        Ghost_Predicate =>
          (for all I in 1 .. Top => Content (I)'Initialized);
   end P2;

   --  Incorrect Model, bad number of parameters

   package P3 is
      type T is private with
        Aggregate => (Empty       => Empty,
                      Add_Unnamed => Append),
        Annotate => (GNATprove, Container_Aggregates, "From_Model");

      function Empty return T with
        Import,
        Global => null;
      procedure Append (X : in out T; E : Element_Type) with
        Global => null,
        Always_Terminates,
        Import;

      function Model (X : T; Y : Integer) return Seqs.T with
        Global => null,
        Import,
        Annotate => (GNATprove, Container_Aggregates, "Model");

   private
      type T_Content is array (Index_Type) of Element_Type with
        Relaxed_Initialization;
      type T is record
         Content : T_Content;
         Top     : Ext_Index;
      end record with
        Ghost_Predicate =>
          (for all I in 1 .. Top => Content (I)'Initialized);
   end P3;

   --  Incorrect Model, return type without aggregates

   package P4 is
      type T is private with
        Aggregate => (Empty       => Empty,
                      Add_Unnamed => Append),
        Annotate => (GNATprove, Container_Aggregates, "From_Model");

      function Empty return T with
        Import,
        Global => null;
      procedure Append (X : in out T; E : Element_Type) with
        Global => null,
        Always_Terminates,
        Import;

      function Model (X : T) return Boolean with
        Global => null,
        Import,
        Annotate => (GNATprove, Container_Aggregates, "Model");

   private
      type T_Content is array (Index_Type) of Element_Type with
        Relaxed_Initialization;
      type T is record
         Content : T_Content;
         Top     : Ext_Index;
      end record with
        Ghost_Predicate =>
          (for all I in 1 .. Top => Content (I)'Initialized);
   end P4;

   --  Incorrect Model, return type with incompatible aggregate kinds

   package P5 is
      type T is private with
        Aggregate => (Empty       => Empty,
                      Add_Unnamed => Append),
        Annotate => (GNATprove, Container_Aggregates, "From_Model");

      function Empty return T with
        Import,
        Global => null;
      procedure Append (X : in out T; E : Element_Type) with
        Global => null,
        Always_Terminates,
        Import;

      function Model (X : T) return Maps.T with
        Global => null,
        Import,
        Annotate => (GNATprove, Container_Aggregates, "Model");

   private
      type T_Content is array (Index_Type) of Element_Type with
        Relaxed_Initialization;
      type T is record
         Content : T_Content;
         Top     : Ext_Index;
      end record with
        Ghost_Predicate =>
          (for all I in 1 .. Top => Content (I)'Initialized);
   end P5;

   --  Incorrect Model, return type with different element types for unnamed

   package P6 is
      type T is private with
        Aggregate => (Empty       => Empty,
                      Add_Unnamed => Append),
        Annotate => (GNATprove, Container_Aggregates, "From_Model");

      function Empty return T with
        Import,
        Global => null;
      procedure Append (X : in out T; E : Integer) with
        Global => null,
        Always_Terminates,
        Import;

      function Model (X : T) return Seqs.T with
        Global => null,
        Import,
        Annotate => (GNATprove, Container_Aggregates, "Model");

   private
      type T_Content is array (Index_Type) of Integer with
        Relaxed_Initialization;
      type T is record
         Content : T_Content;
         Top     : Ext_Index;
      end record with
        Ghost_Predicate =>
          (for all I in 1 .. Top => Content (I)'Initialized);
   end P6;

   --  Incorrect Model, return type with different element types for named

   package P7 is
      type T is private with
        Aggregate => (Empty     => Empty,
                      Add_Named => Insert),
        Annotate => (GNATprove, Container_Aggregates, "From_Model");

      function Empty return T;
      procedure Insert (X : in out T; K : Key_Type; E : Integer) with
        Global => null,
        Always_Terminates,
        Import;

      function Model (X : T) return Maps.T with
        Global => null,
        Import,
        Annotate => (GNATprove, Container_Aggregates, "Model");

   private
      type Pair is record
         K : Key_Type;
         E : Integer;
      end record;
      type T_Cell;
      type T is access T_Cell;
      type T_Cell is record
         P : Pair;
         N : T;
      end record;

      function Empty return T is
        (null);
   end P7;

   --  Incorrect Model, return type with different key types for named

   package P8 is
      type T is private with
        Aggregate => (Empty     => Empty,
                      Add_Named => Insert),
        Annotate => (GNATprove, Container_Aggregates, "From_Model");

      function Empty return T;
      procedure Insert (X : in out T; K : Integer; E : Element_Type) with
        Global => null,
        Always_Terminates,
        Import;

      function Model (X : T) return Maps.T with
        Global => null,
        Import,
        Annotate => (GNATprove, Container_Aggregates, "Model");

   private
      type Pair is record
         K : Integer;
         E : Element_Type;
      end record;
      type T_Cell;
      type T is access T_Cell;
      type T_Cell is record
         P : Pair;
         N : T;
      end record;

      function Empty return T is
        (null);
   end P8;

begin
   null;
end Test_Illegal_Model;
