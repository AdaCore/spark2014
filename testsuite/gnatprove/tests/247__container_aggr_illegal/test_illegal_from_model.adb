procedure Test_Illegal_From_Model with SPARK_Mode is

   type Index_Type is new Integer range 1 .. 100;
   subtype Ext_Index is Index_Type'Base range 0 .. 100;

   type Element_Type is new Integer;

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

   --  Aggregates shall have either an Add_Unnamed or an Add_Named procedure

   package P1 is
      type T is private with
        Aggregate => (Empty          => Empty,
                      New_Indexed    => New_Vector,
                      Assign_Indexed => Assign_Element),
        Annotate => (GNATprove, Container_Aggregates, "From_Model");

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

   --  Model aggregates shall have a Model function

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

   --  Model aggregates with a model function

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

      function Model (X : T) return Seqs.T with
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

   --  Other primitives are not expected

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

      function Model (X : T) return Seqs.T with
        Global => null,
        Import,
        Annotate => (GNATprove, Container_Aggregates, "Model");

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

begin
   null;
end Test_Illegal_From_Model;
