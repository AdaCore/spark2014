procedure Test_Illegal_Maps_Get with SPARK_Mode is

   --  Incorrect Get, no parameters

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

      function Has_Key (X : T; K : Key_Type) return Boolean with
        Annotate => (GNATprove, Container_Aggregates, "Has_Key");

      function Get return Element_Type with
        Global => null,
        Import,
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
   end P1;

   --  Incorrect Get, bad first parameters

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

      function Has_Key (X : T; K : Key_Type) return Boolean with
        Annotate => (GNATprove, Container_Aggregates, "Has_Key");

      function Get (X : Key_Type; K : Key_Type) return Element_Type with
        Global => null,
        Import,
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
   end P2;

   --  Incorrect Get, bad number of parameters

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

      function Has_Key (X : T; K : Key_Type) return Boolean with
        Annotate => (GNATprove, Container_Aggregates, "Has_Key");

      function Get (X : T) return Element_Type with
        Global => null,
        Import,
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
   end P3;

   --  Incorrect Get, bad second parameter

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

      function Has_Key (X : T; K : Key_Type) return Boolean with
        Annotate => (GNATprove, Container_Aggregates, "Has_Key");

      function Get (X : T; K : T) return Element_Type with
        Global => null,
        Import,
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
   end P4;

   --  Incorrect Get, bad return type

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

      function Has_Key (X : T; K : Key_Type) return Boolean with
        Annotate => (GNATprove, Container_Aggregates, "Has_Key");

      function Get (X : T; K : Key_Type) return Key_Type with
        Global => null,
        Import,
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
   end P5;

   --  Incorrect Get, duplicate function

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

      function Has_Key (X : T; K : Key_Type) return Boolean with
        Annotate => (GNATprove, Container_Aggregates, "Has_Key");

      function Get (X : T; K : Key_Type) return Element_Type with
        Global => null,
        Import,
        Annotate => (GNATprove, Container_Aggregates, "Get");

      function Get2 (X : T; K : Key_Type) return Element_Type with
        Global => null,
        Import,
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
   end P6;

   --  Incorrect Get, bad location

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

      function Has_Key (X : T; K : Key_Type) return Boolean with
        Annotate => (GNATprove, Container_Aggregates, "Has_Key");

      package Nested is
         function Get (X : T; K : Key_Type) return Element_Type with
           Global => null,
           Import,
           Annotate => (GNATprove, Container_Aggregates, "Get");
      end Nested;

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
   end P7;

   --  Incorrect Get, bad location of annotate

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

      function Has_Key (X : T; K : Key_Type) return Boolean with
        Annotate => (GNATprove, Container_Aggregates, "Has_Key");

      function Get (X : T; K : Key_Type) return Element_Type with
        Global => null,
        Import;

      function Eq_Key (X, Y : Key_Type) return Boolean is (X = Y) with
        Annotate => (GNATprove, Container_Aggregates, "Equivalent_Keys");

      pragma Annotate (GNATprove, Container_Aggregates, "Get", Get);

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
   end P8;

   --  Incorrect Get, function with side effects

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

      function Has_Key (X : T; K : Key_Type) return Boolean with
        Annotate => (GNATprove, Container_Aggregates, "Has_Key");

      function Get (X : T; K : Key_Type) return Element_Type with
        Side_Effects,
        Global => null,
        Import,
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
   end P9;

   --  Incorrect Get, volatile function

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

      function Has_Key (X : T; K : Key_Type) return Boolean with
        Annotate => (GNATprove, Container_Aggregates, "Has_Key");

      function Get (X : T; K : Key_Type) return Element_Type with
        Volatile_Function,
        Global => null,
        Import,
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
   end P10;

   --  Incorrect Get, SPARK_Mode => Off

   package P11 is
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

      function Has_Key (X : T; K : Key_Type) return Boolean with
        Annotate => (GNATprove, Container_Aggregates, "Has_Key");

      function Get (X : T; K : Key_Type) return Element_Type with
        SPARK_Mode => Off,
        Global => null,
        Import,
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
   end P11;

   --  Incorrect Get, global access

   package P12 is
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

      function Has_Key (X : T; K : Key_Type) return Boolean with
        Annotate => (GNATprove, Container_Aggregates, "Has_Key");

      V : Integer;

      function Get (X : T; K : Key_Type) return Element_Type with
        Global => V,
        Import,
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
   end P12;

begin
   null;
end Test_Illegal_Maps_Get;
