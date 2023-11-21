procedure Test_Illegal_Default_Item with SPARK_Mode is

   --  Incorrect Default_Item, number of parameters

   package P1 is
      Max : constant Natural := 20;
      type Key_Type is range 1 .. 100;
      type Element_Type is new String with
        Predicate => Element_Type'Length <= Max;
      type T is private with
        Aggregate => (Empty       => Empty,
                      Add_Named => Insert),
        Annotate => (GNATprove, Container_Aggregates, "Predefined_Maps");

      function Empty return T;
      procedure Insert (X : in out T; K : Key_Type; E : Element_Type) with
        Global => null,
        Always_Terminates,
        Import;

      function Default_Value (X : Integer) return Element_Type with
        Global => null,
        Import,
        Annotate => (GNATprove, Container_Aggregates, "Default_Item");

      function Get (X : T; K : Key_Type) return Element_Type with
        Annotate => (GNATprove, Container_Aggregates, "Get");

      function Eq_Key (X, Y : Key_Type) return Boolean is (X = Y) with
        Annotate => (GNATprove, Container_Aggregates, "Equivalent_Keys");

   private
      subtype Str_Len is Natural range 0 .. Max;
      type Holder (L : Str_Len := 0) is record
         Elt : Element_Type (1 .. L);
      end record;
      type T_Content is array (Key_Type) of Holder;
      type T is record
         Content : T_Content;
      end record;

      function Empty return T is
        ((Content => (others => (L => 0, Elt => ""))));

      function Get (X : T; K : Key_Type) return Element_Type is
        (X.Content (K).Elt);
   end P1;

   --  Incorrect Default_Item, duplicate function

   package P4 is
      Max : constant Natural := 20;
      type Key_Type is range 1 .. 100;
      type Element_Type is new String with
        Predicate => Element_Type'Length <= Max;
      type T is private with
        Aggregate => (Empty       => Empty,
                      Add_Named => Insert),
        Annotate => (GNATprove, Container_Aggregates, "Predefined_Maps");

      function Empty return T;
      procedure Insert (X : in out T; K : Key_Type; E : Element_Type) with
        Global => null,
        Always_Terminates,
        Import;

      function Default_Value return Element_Type with
        Global => null,
        Import,
        Annotate => (GNATprove, Container_Aggregates, "Default_Item");

      function Default_Value2 return Element_Type with
        Global => null,
        Import,
        Annotate => (GNATprove, Container_Aggregates, "Default_Item");

      function Get (X : T; K : Key_Type) return Element_Type with
        Annotate => (GNATprove, Container_Aggregates, "Get");

      function Eq_Key (X, Y : Key_Type) return Boolean is (X = Y) with
        Annotate => (GNATprove, Container_Aggregates, "Equivalent_Keys");

   private
      subtype Str_Len is Natural range 0 .. Max;
      type Holder (L : Str_Len := 0) is record
         Elt : Element_Type (1 .. L);
      end record;
      type T_Content is array (Key_Type) of Holder;
      type T is record
         Content : T_Content;
      end record;

      function Empty return T is
        ((Content => (others => (L => 0, Elt => ""))));

      function Get (X : T; K : Key_Type) return Element_Type is
        (X.Content (K).Elt);
   end P4;

   --  Incorrect Default_Item, bad location
   --  ??? Here there is no specific complaint, Default_Value is just not
   --  found. It is because Default_Value does not take the container as
   --  parameter so it is difficult to be sure that it is not in the right
   --  scope.

   package P5 is
      Max : constant Natural := 20;
      type Key_Type is range 1 .. 100;
      type Element_Type is new String with
        Predicate => Element_Type'Length <= Max;
      type T is private with
        Aggregate => (Empty       => Empty,
                      Add_Named => Insert),
        Annotate => (GNATprove, Container_Aggregates, "Predefined_Maps");

      function Empty return T;
      procedure Insert (X : in out T; K : Key_Type; E : Element_Type) with
        Global => null,
        Always_Terminates,
        Import;

      package Nested is
         function Default_Value return Element_Type with
           Global => null,
           Import,
           Annotate => (GNATprove, Container_Aggregates, "Default_Item");
      end Nested;

      function Get (X : T; K : Key_Type) return Element_Type with
        Annotate => (GNATprove, Container_Aggregates, "Get");

      function Eq_Key (X, Y : Key_Type) return Boolean is (X = Y) with
        Annotate => (GNATprove, Container_Aggregates, "Equivalent_Keys");

   private
      subtype Str_Len is Natural range 0 .. Max;
      type Holder (L : Str_Len := 0) is record
         Elt : Element_Type (1 .. L);
      end record;
      type T_Content is array (Key_Type) of Holder;
      type T is record
         Content : T_Content;
      end record;

      function Empty return T is
        ((Content => (others => (L => 0, Elt => ""))));

      function Get (X : T; K : Key_Type) return Element_Type is
        (X.Content (K).Elt);
   end P5;

   --  Incorrect Default_Item, bad location of annotate

   package P6 is
      Max : constant Natural := 20;
      type Key_Type is range 1 .. 100;
      type Element_Type is new String with
        Predicate => Element_Type'Length <= Max;
      type T is private with
        Aggregate => (Empty       => Empty,
                      Add_Named => Insert),
        Annotate => (GNATprove, Container_Aggregates, "Predefined_Maps");

      function Empty return T;
      procedure Insert (X : in out T; K : Key_Type; E : Element_Type) with
        Global => null,
        Always_Terminates,
        Import;

      function Default_Value return Element_Type with
        Global => null,
        Import;

      function Get (X : T; K : Key_Type) return Element_Type with
        Annotate => (GNATprove, Container_Aggregates, "Get");

      function Eq_Key (X, Y : Key_Type) return Boolean is (X = Y) with
        Annotate => (GNATprove, Container_Aggregates, "Equivalent_Keys");

      pragma Annotate (GNATprove, Container_Aggregates, "Default_Item", Default_Value);

   private
      subtype Str_Len is Natural range 0 .. Max;
      type Holder (L : Str_Len := 0) is record
         Elt : Element_Type (1 .. L);
      end record;
      type T_Content is array (Key_Type) of Holder;
      type T is record
         Content : T_Content;
      end record;

      function Empty return T is
        ((Content => (others => (L => 0, Elt => ""))));

      function Get (X : T; K : Key_Type) return Element_Type is
        (X.Content (K).Elt);
   end P6;

   --  Incorrect Default_Item, function with side effects

   package P7 is
      Max : constant Natural := 20;
      type Key_Type is range 1 .. 100;
      type Element_Type is new String with
        Predicate => Element_Type'Length <= Max;
      type T is private with
        Aggregate => (Empty       => Empty,
                      Add_Named => Insert),
        Annotate => (GNATprove, Container_Aggregates, "Predefined_Maps");

      function Empty return T;
      procedure Insert (X : in out T; K : Key_Type; E : Element_Type) with
        Global => null,
        Always_Terminates,
        Import;

      function Default_Value return Element_Type with
        Side_Effects,
        Global => null,
        Import,
        Annotate => (GNATprove, Container_Aggregates, "Default_Item");

      function Get (X : T; K : Key_Type) return Element_Type with
        Annotate => (GNATprove, Container_Aggregates, "Get");

      function Eq_Key (X, Y : Key_Type) return Boolean is (X = Y) with
        Annotate => (GNATprove, Container_Aggregates, "Equivalent_Keys");

   private
      subtype Str_Len is Natural range 0 .. Max;
      type Holder (L : Str_Len := 0) is record
         Elt : Element_Type (1 .. L);
      end record;
      type T_Content is array (Key_Type) of Holder;
      type T is record
         Content : T_Content;
      end record;

      function Empty return T is
        ((Content => (others => (L => 0, Elt => ""))));

      function Get (X : T; K : Key_Type) return Element_Type is
        (X.Content (K).Elt);
   end P7;

   --  Incorrect Default_Item, volatile function

   package P8 is
      Max : constant Natural := 20;
      type Key_Type is range 1 .. 100;
      type Element_Type is new String with
        Predicate => Element_Type'Length <= Max;
      type T is private with
        Aggregate => (Empty       => Empty,
                      Add_Named => Insert),
        Annotate => (GNATprove, Container_Aggregates, "Predefined_Maps");

      function Empty return T;
      procedure Insert (X : in out T; K : Key_Type; E : Element_Type) with
        Global => null,
        Always_Terminates,
        Import;

      function Default_Value return Element_Type with
        Volatile_Function,
        Global => null,
        Import,
        Annotate => (GNATprove, Container_Aggregates, "Default_Item");

      function Get (X : T; K : Key_Type) return Element_Type with
        Annotate => (GNATprove, Container_Aggregates, "Get");

      function Eq_Key (X, Y : Key_Type) return Boolean is (X = Y) with
        Annotate => (GNATprove, Container_Aggregates, "Equivalent_Keys");

   private
      subtype Str_Len is Natural range 0 .. Max;
      type Holder (L : Str_Len := 0) is record
         Elt : Element_Type (1 .. L);
      end record;
      type T_Content is array (Key_Type) of Holder;
      type T is record
         Content : T_Content;
      end record;

      function Empty return T is
        ((Content => (others => (L => 0, Elt => ""))));

      function Get (X : T; K : Key_Type) return Element_Type is
        (X.Content (K).Elt);
   end P8;

   --  Incorrect Default_Item, SPARK_Mode => Off
   --  ??? Here there is no specific complaint, Default_Value is just not
   --  found. It is because Default_Value does not take the container as
   --  parameter so it is difficult to know whether it is in SPARK.

   package P9 is
      Max : constant Natural := 20;
      type Key_Type is range 1 .. 100;
      type Element_Type is new String with
        Predicate => Element_Type'Length <= Max;
      type T is private with
        Aggregate => (Empty       => Empty,
                      Add_Named => Insert),
        Annotate => (GNATprove, Container_Aggregates, "Predefined_Maps");

      function Empty return T;
      procedure Insert (X : in out T; K : Key_Type; E : Element_Type) with
        Global => null,
        Always_Terminates,
        Import;

      function Default_Value return Element_Type with
        SPARK_Mode => Off,
        Global => null,
        Import,
        Annotate => (GNATprove, Container_Aggregates, "Default_Item");

      function Get (X : T; K : Key_Type) return Element_Type with
        Annotate => (GNATprove, Container_Aggregates, "Get");

      function Eq_Key (X, Y : Key_Type) return Boolean is (X = Y) with
        Annotate => (GNATprove, Container_Aggregates, "Equivalent_Keys");

   private
      subtype Str_Len is Natural range 0 .. Max;
      type Holder (L : Str_Len := 0) is record
         Elt : Element_Type (1 .. L);
      end record;
      type T_Content is array (Key_Type) of Holder;
      type T is record
         Content : T_Content;
      end record;

      function Empty return T is
        ((Content => (others => (L => 0, Elt => ""))));

      function Get (X : T; K : Key_Type) return Element_Type is
        (X.Content (K).Elt);
   end P9;

   --  Incorrect Default_Item, global access

   package P10 is
      Max : constant Natural := 20;
      type Key_Type is range 1 .. 100;
      type Element_Type is new String with
        Predicate => Element_Type'Length <= Max;
      type T is private with
        Aggregate => (Empty       => Empty,
                      Add_Named => Insert),
        Annotate => (GNATprove, Container_Aggregates, "Predefined_Maps");

      function Empty return T;
      procedure Insert (X : in out T; K : Key_Type; E : Element_Type) with
        Global => null,
        Always_Terminates,
        Import;

      V : Element_Type := "foobar";

      function Default_Value return Element_Type is (V) with
        Annotate => (GNATprove, Container_Aggregates, "Default_Item");

      function Get (X : T; K : Key_Type) return Element_Type with
        Annotate => (GNATprove, Container_Aggregates, "Get");

      function Eq_Key (X, Y : Key_Type) return Boolean is (X = Y) with
        Annotate => (GNATprove, Container_Aggregates, "Equivalent_Keys");

   private
      subtype Str_Len is Natural range 0 .. Max;
      type Holder (L : Str_Len := 0) is record
         Elt : Element_Type (1 .. L);
      end record;
      type T_Content is array (Key_Type) of Holder;
      type T is record
         Content : T_Content;
      end record;

      function Empty return T is
        ((Content => (others => (L => 0, Elt => ""))));

      function Get (X : T; K : Key_Type) return Element_Type is
        (X.Content (K).Elt);
   end P10;

begin
   null;
end Test_Illegal_Default_Item;
