procedure Test_Illegal_Maps_Length with SPARK_Mode is

   --  Incorrect Length, no parameters

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

      function Length return Length_Type with
        Global => null,
        Import,
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
   end P1;

   --  Incorrect Length, bad first parameter

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

      function Length (X : Integer) return Length_Type with
        Global => null,
        Import,
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
   end P2;

   --  Incorrect Length, bad number of parameters

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

      function Length (X : T; I : Integer) return Length_Type with
        Global => null,
        Import,
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
   end P3;

   --  Incorrect Length, bad return type

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

      function Length (X : T) return Boolean with
        Global => null,
        Import,
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
   end P5;

   --  Incorrect Length, duplicate function

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
        Annotate => (GNATprove, Container_Aggregates, "Has_Key");

      function Get (X : T; K : Key_Type) return Element_Type with
        Pre => Has_Key (X, K),
        Annotate => (GNATprove, Container_Aggregates, "Get");

      function Eq_Key (X, Y : Key_Type) return Boolean is (X = Y) with
        Annotate => (GNATprove, Container_Aggregates, "Equivalent_Keys");

      type Length_Type is range 0 .. 100;

      function Length (X : T) return Length_Type with
        Global => null,
        Import,
        Annotate => (GNATprove, Container_Aggregates, "Length");

      function Length2 (X : T) return Length_Type with
        Global => null,
        Import,
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
   end P6;

   --  Incorrect Length, bad location

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

      function Has_Key (X : T; K : Key_Type) return Boolean with
        Annotate => (GNATprove, Container_Aggregates, "Has_Key");

      function Get (X : T; K : Key_Type) return Element_Type with
        Pre => Has_Key (X, K),
        Annotate => (GNATprove, Container_Aggregates, "Get");

      function Eq_Key (X, Y : Key_Type) return Boolean is (X = Y) with
        Annotate => (GNATprove, Container_Aggregates, "Equivalent_Keys");

      type Length_Type is range 0 .. 100;

      package Nested is
         function Length (X : T) return Length_Type with
           Global => null,
           Import,
           Annotate => (GNATprove, Container_Aggregates, "Length");
      end Nested;

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
   end P7;

   --  Incorrect Length, bad location of annotate

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
        Annotate => (GNATprove, Container_Aggregates, "Has_Key");

      function Get (X : T; K : Key_Type) return Element_Type with
        Pre => Has_Key (X, K),
        Annotate => (GNATprove, Container_Aggregates, "Get");

      type Length_Type is range 0 .. 100;

      function Length (X : T) return Length_Type with
        Global => null,
        Import;

      function Eq_Key (X, Y : Key_Type) return Boolean is (X = Y) with
        Annotate => (GNATprove, Container_Aggregates, "Equivalent_Keys");

      pragma Annotate (GNATprove, Container_Aggregates, "Length", Length);

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
   end P8;

   --  Incorrect Length, function with side effects

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
        Side_Effects,
        Global => null,
        Import,
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
   end P9;

   --  Incorrect Length, volatile function

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
        Volatile_Function,
        Global => null,
        Import,
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
   end P10;

   --  Incorrect Length, SPARK_Mode => Off

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
        SPARK_Mode => Off,
        Global => null,
        Import,
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
   end P11;

   --  Incorrect Length, global access

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

      function Has_Key (X : T; K : Key_Type) return Boolean with
        Annotate => (GNATprove, Container_Aggregates, "Has_Key");

      function Get (X : T; K : Key_Type) return Element_Type with
        Pre => Has_Key (X, K),
        Annotate => (GNATprove, Container_Aggregates, "Get");

      function Eq_Key (X, Y : Key_Type) return Boolean is (X = Y) with
        Annotate => (GNATprove, Container_Aggregates, "Equivalent_Keys");

      type Length_Type is range 0 .. 100;

      V : Integer;

      function Length (X : T) return Length_Type with
        Global => V,
        Import,
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
   end P12;

begin
   null;
end Test_Illegal_Maps_Length;
