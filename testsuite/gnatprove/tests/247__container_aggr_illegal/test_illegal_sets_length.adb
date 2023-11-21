procedure Test_Illegal_Sets_Length with SPARK_Mode is

   --  Incorrect Length, no parameters

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

      function Length return Length_Type with
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

   --  Incorrect Length, bad first parameter

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

      function Length (X : Integer) return Length_Type with
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

   --  Incorrect Length, bad number of parameters

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

      function Length (X : T; I : Integer) return Length_Type with
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

   --  Incorrect Length, bad return type

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

      function Length (X : T) return Boolean with
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

   --  Incorrect Length, duplicate function

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

      type Length_Type is range 0 .. 100;

      function Length (X : T) return Length_Type with
        Global => null,
        Import,
        Annotate => (GNATprove, Container_Aggregates, "Length");

      function Length2 (X : T) return Length_Type with
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

   --  Incorrect Length, bad location

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

      package Nested is
         type Length_Type is range 0 .. 100;

         function Length (X : T) return Length_Type with
           Global => null,
           Import,
           Annotate => (GNATprove, Container_Aggregates, "Length");
      end Nested;

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

   --  Incorrect Length, bad location of annotate

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
        Import;

      function Eq_Elem (X, Y : Element_Type) return Boolean is (X = Y) with
        Annotate => (GNATprove, Container_Aggregates, "Equivalent_Elements");

      pragma Annotate (GNATprove, Container_Aggregates, "Length", Length);

   private
      type T_Content is array (Element_Type) of Boolean;
      type T is record
         Content : T_Content;
      end record;

      function Empty return T is
        ((Content => (others => False)));
   end P8;

   --  Incorrect Length, function with side effects

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
        Side_Effects,
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

   --  Incorrect Length, volatile function

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
        Volatile_Function,
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

   --  Incorrect Length, SPARK_Mode => Off

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
        Global => null,
        Import,
        Annotate => (GNATprove, Container_Aggregates, "Contains");

      type Length_Type is range 0 .. 100;

      function Length (X : T) return Length_Type with
        SPARK_Mode => Off,
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

   --  Incorrect Length, global access

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

      function Contains (X : T; E : Element_Type) return Boolean with
        Global => null,
        Import,
        Annotate => (GNATprove, Container_Aggregates, "Contains");

      type Length_Type is range 0 .. 100;

      V : Integer;

      function Length (X : T) return Length_Type with
        Global => V,
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
end Test_Illegal_Sets_Length;
