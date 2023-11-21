procedure Test_Illegal_Maps with SPARK_Mode is

   --  Map aggregate shall have an Add_Named procedure

   package P1 is
      Max : constant Natural := 20;
      type Key_Type is range 1 .. 100;
      type Element_Type is new String with
        Predicate => Element_Type'Length <= Max;
      type T is private with
        Aggregate => (Empty       => Empty,
                      Add_Unnamed => Insert),
        Annotate => (GNATprove, Container_Aggregates, "Predefined_Maps");

      function Empty return T;
      procedure Insert (X : in out T; E : Element_Type) with
        Global => null,
        Always_Terminates,
        Import;

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
   end P1;

   --  Map aggregate shall have a Get function

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
   end P2;

   --  Map aggregate shall have an Equivalent_Keys function

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

   --  Map aggregate shall have either a Has_Key or a Default_Item function

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

   --  Map aggregate shall not have both a Has_Key and a Default_Item function

   package Q1 is
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
        Pre => not Has_Key (X, K),
        Always_Terminates,
        Import;

      function Default_Value return Element_Type is ("") with
        Annotate => (GNATprove, Container_Aggregates, "Default_Item");

      function Has_Key (X : T; K : Key_Type) return Boolean with
        Annotate => (GNATprove, Container_Aggregates, "Has_Key");

      function Get (X : T; K : Key_Type) return Element_Type with
        Pre => Has_Key (X, K),
        Annotate => (GNATprove, Container_Aggregates, "Get");

      function Eq_Key (X, Y : Key_Type) return Boolean is (X = Y) with
        Annotate => (GNATprove, Container_Aggregates, "Equivalent_Keys");

   private
      subtype Str_Len is Natural range 0 .. Max;
      type Holder (L : Str_Len := 0) is record
         Elt : Element_Type (1 .. L);
      end record;
      type Pair is record
         K : Key_Type;
         E : Holder;
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
        (if K = X.P.K then X.P.E.Elt else Get (X.N, K));
   end Q1;

   --  Map aggregate shall not have both a Length and a Default_Item function

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

      function Eq_Key (X, Y : Key_Type) return Boolean is (X = Y) with
        Annotate => (GNATprove, Container_Aggregates, "Equivalent_Keys");

      type Length_Type is range 0 .. 100;

      function Length (X : T) return Length_Type is (100) with
        Annotate => (GNATprove, Container_Aggregates, "Length");

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

   --  With Default_Item, OK

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
   end P6;

   --  with Has_Key, missing Length function, OK

   package Q2 is
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

   private
      subtype Str_Len is Natural range 0 .. Max;
      type Holder (L : Str_Len := 0) is record
         Elt : Element_Type (1 .. L);
      end record;
      type Pair is record
         K : Key_Type;
         E : Holder;
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
        (if K = X.P.K then X.P.E.Elt else Get (X.N, K));
   end Q2;

   --  With Has_Key and a Length function, OK

   package Q3 is
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
      subtype Str_Len is Natural range 0 .. Max;
      type Holder (L : Str_Len := 0) is record
         Elt : Element_Type (1 .. L);
      end record;
      type Pair is record
         K : Key_Type;
         E : Holder;
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
        (if K = X.P.K then X.P.E.Elt else Get (X.N, K));

      function Length (X : T) return Length_Type is
        (if X = null then 0 else Length (X.N) + 1);
   end Q3;

   --  Other primitives are not expected

   package Q4 is
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

      function Contains (X : T; E : Element_Type) return Boolean with
        Annotate => (GNATprove, Container_Aggregates, "Contains");

   private
      subtype Str_Len is Natural range 0 .. Max;
      type Holder (L : Str_Len := 0) is record
         Elt : Element_Type (1 .. L);
      end record;
      type Pair is record
         K : Key_Type;
         E : Holder;
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
        (if K = X.P.K then X.P.E.Elt else Get (X.N, K));

      function Contains (X : T; E : Element_Type) return Boolean is
        (if X = null then False else E = X.P.E.Elt or else Contains (X.N, E));
   end Q4;
begin
   null;
end Test_Illegal_Maps;
