procedure Test_Illegal_Eq_Elements with SPARK_Mode is

   --  Incorrect Eq_Elements, number of parameters

   package P1 is
      type Element_Type is range 1 .. 100;
      type T is private with
        Aggregate => (Empty       => Empty,
                      Add_Unnamed => Insert),
        Annotate => (GNATprove, Container_Aggregates, "Predefined_Sets");

      function Empty return T;
      procedure Insert (X : in out T; E : Element_Type) with
        Global => null,
        Always_Terminates,
        Import;

      function Contains (X : T; E : Element_Type) return Boolean with
        Global => null,
        Import,
        Annotate => (GNATprove, Container_Aggregates, "Contains");

      type Length_Type is range 0 .. 100;

      function Length (X : T) return Length_Type with
        Global => null,
        Import,
        Annotate => (GNATprove, Container_Aggregates, "Length");

      function Eq_Elem return Boolean with
        Global => null,
        Import,
        Annotate => (GNATprove, Container_Aggregates, "Equivalent_Elements");

   private
      type T_Content is array (Element_Type) of Boolean;
      type T is record
         Content : T_Content;
      end record;

      function Empty return T is
        ((Content => (others => False)));
   end P1;

   --  Incorrect Eq_Elements, different parameters

   package P2 is
      type Element_Type is range 1 .. 100;
      type T is private with
        Aggregate => (Empty       => Empty,
                      Add_Unnamed => Insert),
        Annotate => (GNATprove, Container_Aggregates, "Predefined_Sets");

      function Empty return T;
      procedure Insert (X : in out T; E : Element_Type) with
        Global => null,
        Always_Terminates,
        Import;

      function Contains (X : T; E : Element_Type) return Boolean with
        Global => null,
        Import,
        Annotate => (GNATprove, Container_Aggregates, "Contains");

      type Length_Type is range 0 .. 100;

      function Length (X : T) return Length_Type with
        Global => null,
        Import,
        Annotate => (GNATprove, Container_Aggregates, "Length");

      function Eq_Elem (X : Integer; Y : Element_Type) return Boolean with
        Global => null,
        Import,
        Annotate => (GNATprove, Container_Aggregates, "Equivalent_Elements");

   private
      type T_Content is array (Element_Type) of Boolean;
      type T is record
         Content : T_Content;
      end record;

      function Empty return T is
        ((Content => (others => False)));
   end P2;

   --  Incorrect Eq_Elements, bad return type

   package P3 is
      type Element_Type is range 1 .. 100;
      type T is private with
        Aggregate => (Empty       => Empty,
                      Add_Unnamed => Insert),
        Annotate => (GNATprove, Container_Aggregates, "Predefined_Sets");

      function Empty return T;
      procedure Insert (X : in out T; E : Element_Type) with
        Global => null,
        Always_Terminates,
        Import;

      function Contains (X : T; E : Element_Type) return Boolean with
        Global => null,
        Import,
        Annotate => (GNATprove, Container_Aggregates, "Contains");

      type Length_Type is range 0 .. 100;

      function Length (X : T) return Length_Type with
        Global => null,
        Import,
        Annotate => (GNATprove, Container_Aggregates, "Length");

      function Eq_Elem (X, Y : Element_Type) return Integer with
        Global => null,
        Import,
        Annotate => (GNATprove, Container_Aggregates, "Equivalent_Elements");

   private
      type T_Content is array (Element_Type) of Boolean;
      type T is record
         Content : T_Content;
      end record;

      function Empty return T is
        ((Content => (others => False)));
   end P3;

   --  Incorrect Eq_Elements, duplicate function

   package P4 is
      type Element_Type is range 1 .. 100;
      type T is private with
        Aggregate => (Empty       => Empty,
                      Add_Unnamed => Insert),
        Annotate => (GNATprove, Container_Aggregates, "Predefined_Sets");

      function Empty return T;
      procedure Insert (X : in out T; E : Element_Type) with
        Global => null,
        Always_Terminates,
        Import;

      function Contains (X : T; E : Element_Type) return Boolean with
        Global => null,
        Import,
        Annotate => (GNATprove, Container_Aggregates, "Contains");

      type Length_Type is range 0 .. 100;

      function Length (X : T) return Length_Type with
        Global => null,
        Import,
        Annotate => (GNATprove, Container_Aggregates, "Length");

      function Eq_Elem (X, Y : Element_Type) return Boolean with
        Global => null,
        Import,
        Annotate => (GNATprove, Container_Aggregates, "Equivalent_Elements");

      function Eq_Elem2 (X, Y : Element_Type) return Boolean with
        Global => null,
        Import,
        Annotate => (GNATprove, Container_Aggregates, "Equivalent_Elements");

   private
      type T_Content is array (Element_Type) of Boolean;
      type T is record
         Content : T_Content;
      end record;

      function Empty return T is
        ((Content => (others => False)));
   end P4;

   --  Incorrect Eq_Elements, bad location
   --  ??? Here there is no specific complaint, Eq_Elem is just not found. It
   --  is because Eq_Elem does not take the container as parameter so it is
   --  difficult to be sure that it is not in the right scope.

   package P5 is
      type Element_Type is range 1 .. 100;
      type T is private with
        Aggregate => (Empty       => Empty,
                      Add_Unnamed => Insert),
        Annotate => (GNATprove, Container_Aggregates, "Predefined_Sets");

      function Empty return T;
      procedure Insert (X : in out T; E : Element_Type) with
        Global => null,
        Always_Terminates,
        Import;

      function Contains (X : T; E : Element_Type) return Boolean with
        Global => null,
        Import,
        Annotate => (GNATprove, Container_Aggregates, "Contains");

      type Length_Type is range 0 .. 100;

      function Length (X : T) return Length_Type with
        Global => null,
        Import,
        Annotate => (GNATprove, Container_Aggregates, "Length");

      package Nested is
         function Eq_Elem (X, Y : Element_Type) return Boolean with
           Global => null,
           Import,
           Annotate => (GNATprove, Container_Aggregates, "Equivalent_Elements");
      end Nested;

   private
      type T_Content is array (Element_Type) of Boolean;
      type T is record
         Content : T_Content;
      end record;

      function Empty return T is
        ((Content => (others => False)));
   end P5;

   --  Incorrect Eq_Elements, bad location of annotate

   package P6 is
      type Element_Type is range 1 .. 100;
      type T is private with
        Aggregate => (Empty       => Empty,
                      Add_Unnamed => Insert),
        Annotate => (GNATprove, Container_Aggregates, "Predefined_Sets");

      function Empty return T;
      procedure Insert (X : in out T; E : Element_Type) with
        Global => null,
        Always_Terminates,
        Import;

      function Contains (X : T; E : Element_Type) return Boolean with
        Global => null,
        Import,
        Annotate => (GNATprove, Container_Aggregates, "Contains");

      function Eq_Elem (X, Y : Element_Type) return Boolean with
        Global => null,
        Import;

      type Length_Type is range 0 .. 100;

      function Length (X : T) return Length_Type with
        Global => null,
        Import,
        Annotate => (GNATprove, Container_Aggregates, "Length");

      pragma Annotate (GNATprove, Container_Aggregates, "Equivalent_Elements", Eq_Elem);

   private
      type T_Content is array (Element_Type) of Boolean;
      type T is record
         Content : T_Content;
      end record;

      function Empty return T is
        ((Content => (others => False)));
   end P6;

   --  Incorrect Eq_Elements, function with side effects

   package P7 is
      type Element_Type is range 1 .. 100;
      type T is private with
        Aggregate => (Empty       => Empty,
                      Add_Unnamed => Insert),
        Annotate => (GNATprove, Container_Aggregates, "Predefined_Sets");

      function Empty return T;
      procedure Insert (X : in out T; E : Element_Type) with
        Global => null,
        Always_Terminates,
        Import;

      function Contains (X : T; E : Element_Type) return Boolean with
        Global => null,
        Import,
        Annotate => (GNATprove, Container_Aggregates, "Contains");

      type Length_Type is range 0 .. 100;

      function Length (X : T) return Length_Type with
        Global => null,
        Import,
        Annotate => (GNATprove, Container_Aggregates, "Length");

      function Eq_Elem (X, Y : Element_Type) return Boolean with
        Side_Effects,
        Global => null,
        Import,
        Annotate => (GNATprove, Container_Aggregates, "Equivalent_Elements");

   private
      type T_Content is array (Element_Type) of Boolean;
      type T is record
         Content : T_Content;
      end record;

      function Empty return T is
        ((Content => (others => False)));
   end P7;

   --  Incorrect Eq_Elements, volatile function

   package P8 is
      type Element_Type is range 1 .. 100;
      type T is private with
        Aggregate => (Empty       => Empty,
                      Add_Unnamed => Insert),
        Annotate => (GNATprove, Container_Aggregates, "Predefined_Sets");

      function Empty return T;
      procedure Insert (X : in out T; E : Element_Type) with
        Global => null,
        Always_Terminates,
        Import;

      function Contains (X : T; E : Element_Type) return Boolean with
        Global => null,
        Import,
        Annotate => (GNATprove, Container_Aggregates, "Contains");

      type Length_Type is range 0 .. 100;

      function Length (X : T) return Length_Type with
        Global => null,
        Import,
        Annotate => (GNATprove, Container_Aggregates, "Length");

      function Eq_Elem (X, Y : Element_Type) return Boolean with
        Volatile_Function,
        Global => null,
        Import,
        Annotate => (GNATprove, Container_Aggregates, "Equivalent_Elements");

   private
      type T_Content is array (Element_Type) of Boolean;
      type T is record
         Content : T_Content;
      end record;

      function Empty return T is
        ((Content => (others => False)));
   end P8;

   --  Incorrect Eq_Elements, SPARK_Mode => Off
   --  ??? Here there is no specific complaint, Eq_Elem is just not found. It
   --  is because Eq_Elem does not take the container as parameter so it is
   --  difficult to know whether it is in SPARK.

   package P9 is
      type Element_Type is range 1 .. 100;
      type T is private with
        Aggregate => (Empty       => Empty,
                      Add_Unnamed => Insert),
        Annotate => (GNATprove, Container_Aggregates, "Predefined_Sets");

      function Empty return T;
      procedure Insert (X : in out T; E : Element_Type) with
        Global => null,
        Always_Terminates,
        Import;

      function Contains (X : T; E : Element_Type) return Boolean with
        Global => null,
        Import,
        Annotate => (GNATprove, Container_Aggregates, "Contains");

      type Length_Type is range 0 .. 100;

      function Length (X : T) return Length_Type with
        Global => null,
        Import,
        Annotate => (GNATprove, Container_Aggregates, "Length");

      function Eq_Elem (X, Y : Element_Type) return Boolean with
        SPARK_Mode => Off,
        Global => null,
        Import,
        Annotate => (GNATprove, Container_Aggregates, "Equivalent_Elements");

   private
      type T_Content is array (Element_Type) of Boolean;
      type T is record
         Content : T_Content;
      end record;

      function Empty return T is
        ((Content => (others => False)));
   end P9;

   --  Incorrect Eq_Elements, global access

   package P10 is
      type Element_Type is range 1 .. 100;
      type T is private with
        Aggregate => (Empty       => Empty,
                      Add_Unnamed => Insert),
        Annotate => (GNATprove, Container_Aggregates, "Predefined_Sets");

      function Empty return T;
      procedure Insert (X : in out T; E : Element_Type) with
        Global => null,
        Always_Terminates,
        Import;

      function Contains (X : T; E : Element_Type) return Boolean with
        Global => null,
        Import,
        Annotate => (GNATprove, Container_Aggregates, "Contains");

      type Length_Type is range 0 .. 100;

      function Length (X : T) return Length_Type with
        Global => null,
        Import,
        Annotate => (GNATprove, Container_Aggregates, "Length");

      V : Integer;

      function Eq_Elem (X, Y : Element_Type) return Boolean with
        Global => V,
        Import,
        Annotate => (GNATprove, Container_Aggregates, "Equivalent_Elements");

   private
      type T_Content is array (Element_Type) of Boolean;
      type T is record
         Content : T_Content;
      end record;

      function Empty return T is
        ((Content => (others => False)));
   end P10;

begin
   null;
end Test_Illegal_Eq_Elements;
