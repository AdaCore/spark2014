procedure Test_Illegal_Has_Key with SPARK_Mode is

   --  Incorrect Has_Key, no parameters

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

      function Has_Key return Boolean with
        Global => null,
        Import,
        Annotate => (GNATprove, Container_Aggregates, "Has_Key");

      function Get (X : T; K : Key_Type) return Element_Type with
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

      function Get (X : T; K : Key_Type) return Element_Type is
        (if K = X.P.K then X.P.E.Elt else Get (X.N, K));
   end P1;

   --  Incorrect Has_Key, bad first parameters

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

      function Has_Key (X : Boolean; K : Key_Type) return Boolean with
        Global => null,
        Import,
        Annotate => (GNATprove, Container_Aggregates, "Has_Key");

      function Get (X : T; K : Key_Type) return Element_Type with
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

      function Get (X : T; K : Key_Type) return Element_Type is
        (if K = X.P.K then X.P.E.Elt else Get (X.N, K));
   end P2;

   --  Incorrect Has_Key, bad number of parameters

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

      function Has_Key (X : T) return Boolean with
        Global => null,
        Import,
        Annotate => (GNATprove, Container_Aggregates, "Has_Key");

      function Get (X : T; K : Key_Type) return Element_Type with
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

      function Get (X : T; K : Key_Type) return Element_Type is
        (if K = X.P.K then X.P.E.Elt else Get (X.N, K));
   end P3;

   --  Incorrect Has_Key, bad second parameter

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

      function Has_Key (X : T; K : Element_Type) return Boolean with
        Global => null,
        Import,
        Annotate => (GNATprove, Container_Aggregates, "Has_Key");

      function Get (X : T; K : Key_Type) return Element_Type with
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

      function Get (X : T; K : Key_Type) return Element_Type is
        (if K = X.P.K then X.P.E.Elt else Get (X.N, K));
   end P4;

   --  Incorrect Has_Key, bad return type

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

      function Has_Key (X : T; K : Key_Type) return Integer with
        Global => null,
        Import,
        Annotate => (GNATprove, Container_Aggregates, "Has_Key");

      function Get (X : T; K : Key_Type) return Element_Type with
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

      function Get (X : T; K : Key_Type) return Element_Type is
        (if K = X.P.K then X.P.E.Elt else Get (X.N, K));
   end P5;

   --  Incorrect Has_Key, duplicate function

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
        Pre => not Has_Key (X, K),
        Always_Terminates,
        Import;

      function Has_Key (X : T; K : Key_Type) return Boolean with
        Global => null,
        Import,
        Annotate => (GNATprove, Container_Aggregates, "Has_Key");

      function Has_Key2 (X : T; K : Key_Type) return Boolean with
        Global => null,
        Import,
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

      function Get (X : T; K : Key_Type) return Element_Type is
        (if K = X.P.K then X.P.E.Elt else Get (X.N, K));
   end P6;

   --  Incorrect Has_Key, bad location

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
        Pre => not Has_Key (X, K),
        Always_Terminates,
        Import;

      package Nested is
         function Has_Key (X : T; K : Key_Type) return Boolean with
           Global => null,
           Import,
           Annotate => (GNATprove, Container_Aggregates, "Has_Key");
      end Nested;
      use Nested;

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

      function Get (X : T; K : Key_Type) return Element_Type is
        (if K = X.P.K then X.P.E.Elt else Get (X.N, K));
   end P7;

   --  Incorrect Has_Key, bad location of annotate

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
        Pre => not Has_Key (X, K),
        Always_Terminates,
        Import;

      function Has_Key (X : T; K : Key_Type) return Boolean with
        Global => null,
        Import;

      function Get (X : T; K : Key_Type) return Element_Type with
        Pre => Has_Key (X, K),
        Annotate => (GNATprove, Container_Aggregates, "Get");

      function Eq_Key (X, Y : Key_Type) return Boolean is (X = Y) with
        Annotate => (GNATprove, Container_Aggregates, "Equivalent_Keys");

      pragma Annotate (GNATprove, Container_Aggregates, "Has_Key", Has_Key);

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

      function Get (X : T; K : Key_Type) return Element_Type is
        (if K = X.P.K then X.P.E.Elt else Get (X.N, K));
   end P8;

   --  Incorrect Has_Key, function with side effects

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
        Side_Effects,
        Global => null,
        Import,
        Annotate => (GNATprove, Container_Aggregates, "Has_Key");

      function Get (X : T; K : Key_Type) return Element_Type with
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

      function Get (X : T; K : Key_Type) return Element_Type is
        (if K = X.P.K then X.P.E.Elt else Get (X.N, K));
   end P9;

   --  Incorrect Has_Key, volatile function

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
        Volatile_Function,
        Global => null,
        Import,
        Annotate => (GNATprove, Container_Aggregates, "Has_Key");

      function Get (X : T; K : Key_Type) return Element_Type with
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

      function Get (X : T; K : Key_Type) return Element_Type is
        (if K = X.P.K then X.P.E.Elt else Get (X.N, K));
   end P10;

   --  Incorrect Has_Key, SPARK_Mode => Off

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
        SPARK_Mode => Off,
        Global => null,
        Import,
        Annotate => (GNATprove, Container_Aggregates, "Has_Key");

      function Get (X : T; K : Key_Type) return Element_Type with
        Global => null,
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

      function Get (X : T; K : Key_Type) return Element_Type is
        (if K = X.P.K then X.P.E.Elt else Get (X.N, K));
   end P11;

   --  Incorrect Has_Key, global access

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
        Pre => not Has_Key (X, K),
        Always_Terminates,
        Import;

      V : Integer;

      function Has_Key (X : T; K : Key_Type) return Boolean with
        Global => V,
        Import,
        Annotate => (GNATprove, Container_Aggregates, "Has_Key");

      function Get (X : T; K : Key_Type) return Element_Type with
        Global => null,
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

      function Get (X : T; K : Key_Type) return Element_Type is
        (if K = X.P.K then X.P.E.Elt else Get (X.N, K));
   end P12;

begin
   null;
end Test_Illegal_Has_Key;
