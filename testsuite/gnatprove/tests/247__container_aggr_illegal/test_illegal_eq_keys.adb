procedure Test_Illegal_Eq_Keys with SPARK_Mode is

   --  Incorrect Eq_Keys, number of parameters

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

      function Default_Value return Element_Type is ("") with
        Annotate => (GNATprove, Container_Aggregates, "Default_Item");

      function Get (X : T; K : Key_Type) return Element_Type with
        Annotate => (GNATprove, Container_Aggregates, "Get");

      function Eq_Key (X : Key_Type) return Boolean with
        Global => null,
        Import,
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

   --  Incorrect Eq_Keys, different parameters

   package P2 is
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

      function Default_Value return Element_Type is ("") with
        Annotate => (GNATprove, Container_Aggregates, "Default_Item");

      function Get (X : T; K : Key_Type) return Element_Type with
        Annotate => (GNATprove, Container_Aggregates, "Get");

      function Eq_Key (X : Boolean; Y : Key_Type) return Boolean with
        Global => null,
        Import,
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
   end P2;

   --  Incorrect Eq_Keys, bad return type

   package P3 is
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

      function Default_Value return Element_Type is ("") with
        Annotate => (GNATprove, Container_Aggregates, "Default_Item");

      function Get (X : T; K : Key_Type) return Element_Type with
        Annotate => (GNATprove, Container_Aggregates, "Get");

      function Eq_Key (X, Y : Key_Type) return Integer with
        Global => null,
        Import,
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
   end P3;

   --  Incorrect Eq_Keys, duplicate function

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

      function Default_Value return Element_Type is ("") with
        Annotate => (GNATprove, Container_Aggregates, "Default_Item");

      function Get (X : T; K : Key_Type) return Element_Type with
        Annotate => (GNATprove, Container_Aggregates, "Get");

      function Eq_Key (X, Y : Key_Type) return Boolean with
        Global => null,
        Import,
        Annotate => (GNATprove, Container_Aggregates, "Equivalent_Keys");

      function Eq_Key2 (X, Y : Key_Type) return Boolean with
        Global => null,
        Import,
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

   --  Incorrect Eq_Keys, bad location
   --  ??? Here there is no specific complaint, Eq_Elem is just not found. It
   --  is because Eq_Elem does not take the container as parameter so it is
   --  difficult to be sure that it is not in the right scope.

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

      function Default_Value return Element_Type is ("") with
        Annotate => (GNATprove, Container_Aggregates, "Default_Item");

      function Get (X : T; K : Key_Type) return Element_Type with
        Annotate => (GNATprove, Container_Aggregates, "Get");

      package Nested is
         function Eq_Key (X, Y : Key_Type) return Boolean with
           Global => null,
           Import,
           Annotate => (GNATprove, Container_Aggregates, "Equivalent_Keys");
      end Nested;

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

   --  Incorrect Eq_Keys, bad location of annotate

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

      function Default_Value return Element_Type is ("") with
        Annotate => (GNATprove, Container_Aggregates, "Default_Item");

      function Eq_Key (X, Y : Key_Type) return Boolean with
        Global => null,
        Import;

      function Get (X : T; K : Key_Type) return Element_Type with
        Annotate => (GNATprove, Container_Aggregates, "Get");

      pragma Annotate (GNATprove, Container_Aggregates, "Equivalent_Keys", Eq_Key);

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

   --  Incorrect Eq_Keys, function with side effects

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

      function Default_Value return Element_Type is ("") with
        Annotate => (GNATprove, Container_Aggregates, "Default_Item");

      function Get (X : T; K : Key_Type) return Element_Type with
        Annotate => (GNATprove, Container_Aggregates, "Get");

      function Eq_Key (X, Y : Key_Type) return Boolean with
        Side_Effects,
        Global => null,
        Import,
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

   --  Incorrect Eq_Keys, volatile function

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

      function Default_Value return Element_Type is ("") with
        Annotate => (GNATprove, Container_Aggregates, "Default_Item");

      function Get (X : T; K : Key_Type) return Element_Type with
        Annotate => (GNATprove, Container_Aggregates, "Get");

      function Eq_Key (X, Y : Key_Type) return Boolean with
        Volatile_Function,
        Global => null,
        Import,
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

   --  Incorrect Eq_Keys, SPARK_Mode => Off
   --  ??? Here there is no specific complaint, Eq_Elem is just not found. It
   --  is because Eq_Elem does not take the container as parameter so it is
   --  difficult to know whether it is in SPARK.

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

      function Default_Value return Element_Type is ("") with
        Annotate => (GNATprove, Container_Aggregates, "Default_Item");

      function Get (X : T; K : Key_Type) return Element_Type with
        Annotate => (GNATprove, Container_Aggregates, "Get");

      function Eq_Key (X, Y : Key_Type) return Boolean with
        SPARK_Mode => Off,
        Global => null,
        Import,
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

   --  Incorrect Eq_Keys, global access

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

      function Default_Value return Element_Type is ("") with
        Annotate => (GNATprove, Container_Aggregates, "Default_Item");

      function Get (X : T; K : Key_Type) return Element_Type with
        Annotate => (GNATprove, Container_Aggregates, "Get");

      V : Integer;

      function Eq_Key (X, Y : Key_Type) return Boolean with
        Global => V,
        Import,
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
end Test_Illegal_Eq_Keys;
