procedure Test_Illegal_Contains with SPARK_Mode is

   --  Incorrect Contains, no parameters

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

      function Contains return Boolean with
        Global => null,
        Import,
        Annotate => (GNATprove, Container_Aggregates, "Contains");

      type Length_Type is range 0 .. 100;

      function Length (X : T) return Length_Type with
        Global => null,
        Import,
        Annotate => (GNATprove, Container_Aggregates, "Length");

      function Eq_Elem (X, Y : Element_Type) return Boolean is (X = Y) with
        Annotate => (GNATprove, Container_Aggregates, "Equivalent_Elements");

   private
      type T_Content is array (Element_Type) of Boolean;
      type T is record
         Content : T_Content;
      end record;

      function Empty return T is
        ((Content => (others => False)));
   end P1;

   --  Incorrect Contains, bad first parameters

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

      function Contains (X : Integer; E : Element_Type) return Boolean with
        Global => null,
        Import,
        Annotate => (GNATprove, Container_Aggregates, "Contains");

      type Length_Type is range 0 .. 100;

      function Length (X : T) return Length_Type with
        Global => null,
        Import,
        Annotate => (GNATprove, Container_Aggregates, "Length");

      function Eq_Elem (X, Y : Element_Type) return Boolean is (X = Y) with
        Annotate => (GNATprove, Container_Aggregates, "Equivalent_Elements");

   private
      type T_Content is array (Element_Type) of Boolean;
      type T is record
         Content : T_Content;
      end record;

      function Empty return T is
        ((Content => (others => False)));
   end P2;

   --  Incorrect Contains, bad number of parameters

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

      function Contains (X : T) return Boolean with
        Global => null,
        Import,
        Annotate => (GNATprove, Container_Aggregates, "Contains");

      type Length_Type is range 0 .. 100;

      function Length (X : T) return Length_Type with
        Global => null,
        Import,
        Annotate => (GNATprove, Container_Aggregates, "Length");

      function Eq_Elem (X, Y : Element_Type) return Boolean is (X = Y) with
        Annotate => (GNATprove, Container_Aggregates, "Equivalent_Elements");

   private
      type T_Content is array (Element_Type) of Boolean;
      type T is record
         Content : T_Content;
      end record;

      function Empty return T is
        ((Content => (others => False)));
   end P3;

   --  Incorrect Contains, bad second parameter

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

      function Contains (X : T; I : Integer) return Boolean with
        Global => null,
        Import,
        Annotate => (GNATprove, Container_Aggregates, "Contains");

      type Length_Type is range 0 .. 100;

      function Length (X : T) return Length_Type with
        Global => null,
        Import,
        Annotate => (GNATprove, Container_Aggregates, "Length");

      function Eq_Elem (X, Y : Element_Type) return Boolean is (X = Y) with
        Annotate => (GNATprove, Container_Aggregates, "Equivalent_Elements");

   private
      type T_Content is array (Element_Type) of Boolean;
      type T is record
         Content : T_Content;
      end record;

      function Empty return T is
        ((Content => (others => False)));
   end P4;

   --  Incorrect Contains, bad return type

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

      function Contains (X : T; E : Element_Type) return Integer with
        Global => null,
        Import,
        Annotate => (GNATprove, Container_Aggregates, "Contains");

      type Length_Type is range 0 .. 100;

      function Length (X : T) return Length_Type with
        Global => null,
        Import,
        Annotate => (GNATprove, Container_Aggregates, "Length");

      function Eq_Elem (X, Y : Element_Type) return Boolean is (X = Y) with
        Annotate => (GNATprove, Container_Aggregates, "Equivalent_Elements");

   private
      type T_Content is array (Element_Type) of Boolean;
      type T is record
         Content : T_Content;
      end record;

      function Empty return T is
        ((Content => (others => False)));
   end P5;

   --  Incorrect Contains, duplicate function

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

      function Contains_2 (X : T; E : Element_Type) return Boolean with
        Global => null,
        Import,
        Annotate => (GNATprove, Container_Aggregates, "Contains");

      type Length_Type is range 0 .. 100;

      function Length (X : T) return Length_Type with
        Global => null,
        Import,
        Annotate => (GNATprove, Container_Aggregates, "Length");

      function Eq_Elem (X, Y : Element_Type) return Boolean is (X = Y) with
        Annotate => (GNATprove, Container_Aggregates, "Equivalent_Elements");

   private
      type T_Content is array (Element_Type) of Boolean;
      type T is record
         Content : T_Content;
      end record;

      function Empty return T is
        ((Content => (others => False)));
   end P6;

   --  Incorrect Contains, bad location

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

      package Nested is
         function Contains (X : T; E : Element_Type) return Boolean with
           Global => null,
           Import,
           Annotate => (GNATprove, Container_Aggregates, "Contains");
      end Nested;

      type Length_Type is range 0 .. 100;

      function Length (X : T) return Length_Type with
        Global => null,
        Import,
        Annotate => (GNATprove, Container_Aggregates, "Length");

      function Eq_Elem (X, Y : Element_Type) return Boolean is (X = Y) with
        Annotate => (GNATprove, Container_Aggregates, "Equivalent_Elements");

   private
      type T_Content is array (Element_Type) of Boolean;
      type T is record
         Content : T_Content;
      end record;

      function Empty return T is
        ((Content => (others => False)));
   end P7;

   --  Incorrect Contains, bad location of annotate

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
        Import;

      type Length_Type is range 0 .. 100;

      function Length (X : T) return Length_Type with
        Global => null,
        Import,
        Annotate => (GNATprove, Container_Aggregates, "Length");
      pragma Annotate (GNATprove, Container_Aggregates, "Contains", Contains);

      function Eq_Elem (X, Y : Element_Type) return Boolean is (X = Y) with
        Annotate => (GNATprove, Container_Aggregates, "Equivalent_Elements");

   private
      type T_Content is array (Element_Type) of Boolean;
      type T is record
         Content : T_Content;
      end record;

      function Empty return T is
        ((Content => (others => False)));
   end P8;

   --  Incorrect Contains, function with side effects

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
        Side_Effects,
        Global => null,
        Import,
        Annotate  => (GNATprove, Container_Aggregates, "Contains");

      type Length_Type is range 0 .. 100;

      function Length (X : T) return Length_Type with
        Global => null,
        Import,
        Annotate => (GNATprove, Container_Aggregates, "Length");

      function Eq_Elem (X, Y : Element_Type) return Boolean is (X = Y) with
        Annotate => (GNATprove, Container_Aggregates, "Equivalent_Elements");

   private
      type T_Content is array (Element_Type) of Boolean;
      type T is record
         Content : T_Content;
      end record;

      function Empty return T is
        ((Content => (others => False)));
   end P9;

   --  Incorrect Contains, volatile function

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
        Volatile_Function,
        Global => null,
        Import,
        Annotate  => (GNATprove, Container_Aggregates, "Contains");

      type Length_Type is range 0 .. 100;

      function Length (X : T) return Length_Type with
        Global => null,
        Import,
        Annotate => (GNATprove, Container_Aggregates, "Length");

      function Eq_Elem (X, Y : Element_Type) return Boolean is (X = Y) with
        Annotate => (GNATprove, Container_Aggregates, "Equivalent_Elements");

   private
      type T_Content is array (Element_Type) of Boolean;
      type T is record
         Content : T_Content;
      end record;

      function Empty return T is
        ((Content => (others => False)));
   end P10;

   --  Incorrect Contains, SPARK_Mode => Off

   package P11 is
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
        SPARK_Mode => Off,
        Global => null,
        Import,
        Annotate  => (GNATprove, Container_Aggregates, "Contains");

      type Length_Type is range 0 .. 100;

      function Length (X : T) return Length_Type with
        Global => null,
        Import,
        Annotate => (GNATprove, Container_Aggregates, "Length");

      function Eq_Elem (X, Y : Element_Type) return Boolean is (X = Y) with
        Annotate => (GNATprove, Container_Aggregates, "Equivalent_Elements");

   private
      type T_Content is array (Element_Type) of Boolean;
      type T is record
         Content : T_Content;
      end record;

      function Empty return T is
        ((Content => (others => False)));
   end P11;

   --  Incorrect Contains, global access

   package P12 is
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

      V : Integer;

      function Contains (X : T; E : Element_Type) return Boolean with
        Global => V,
        Import,
        Annotate  => (GNATprove, Container_Aggregates, "Contains");

      type Length_Type is range 0 .. 100;

      function Length (X : T) return Length_Type with
        Global => null,
        Import,
        Annotate => (GNATprove, Container_Aggregates, "Length");

      function Eq_Elem (X, Y : Element_Type) return Boolean is (X = Y) with
        Annotate => (GNATprove, Container_Aggregates, "Equivalent_Elements");

   private
      type T_Content is array (Element_Type) of Boolean;
      type T is record
         Content : T_Content;
      end record;

      function Empty return T is
        ((Content => (others => False)));
   end P12;

begin
   null;
end Test_Illegal_Contains;
