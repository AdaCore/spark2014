
procedure Test_Illegal_Empty with SPARK_Mode is

   --  Empty function with side effects

   package P1 is
      type Element_Type is range 1 .. 100;
      type T is private with
        Aggregate => (Empty       => Empty,
                      Add_Unnamed => Insert),
        Annotate => (GNATprove, Container_Aggregates, "Predefined_Sets");

      function Empty return T with
        Global => null,
        Side_Effects,
        Import;
      procedure Insert (X : in out T; E : Element_Type) with
        Global => null,
        Always_Terminates,
        Import;

      function Contains (X : T; E : Element_Type) return Boolean with
        Annotate => (GNATprove, Container_Aggregates, "Contains");

      function Eq_Elem (X, Y : Element_Type) return Boolean is (X = Y) with
        Annotate => (GNATprove, Container_Aggregates, "Equivalent_Elements");

   private
      type T_Content is array (Element_Type) of Boolean;
      type T is record
         Content : T_Content;
      end record;

      function Contains (X : T; E : Element_Type) return Boolean is
        (X.Content (E));
   end P1;

   --  Volatile Empty function

   package P2 is
      type Element_Type is range 1 .. 100;
      type T is private with
        Aggregate => (Empty       => Empty,
                      Add_Unnamed => Insert),
        Annotate => (GNATprove, Container_Aggregates, "Predefined_Sets");

      function Empty return T with Volatile_Function;
      procedure Insert (X : in out T; E : Element_Type) with
        Global => null,
        Always_Terminates,
        Import;

      function Contains (X : T; E : Element_Type) return Boolean with
        Annotate => (GNATprove, Container_Aggregates, "Contains");

      function Eq_Elem (X, Y : Element_Type) return Boolean is (X = Y) with
        Annotate => (GNATprove, Container_Aggregates, "Equivalent_Elements");

   private
      type T_Content is array (Element_Type) of Boolean;
      type T is record
         Content : T_Content;
      end record;

      function Empty return T is
        ((Content => (others => False)));

      function Contains (X : T; E : Element_Type) return Boolean is
        (X.Content (E));
   end P2;

   --  Empty function which accesses global data

   package P3 is
      type Element_Type is range 1 .. 100;
      type T is private with
        Aggregate => (Empty       => Empty,
                      Add_Unnamed => Insert),
        Annotate => (GNATprove, Container_Aggregates, "Predefined_Sets");

      V : Integer;

      function Empty return T with Global => V;
      procedure Insert (X : in out T; E : Element_Type) with
        Global => null,
        Always_Terminates,
        Import;

      function Contains (X : T; E : Element_Type) return Boolean with
        Annotate => (GNATprove, Container_Aggregates, "Contains");

      function Eq_Elem (X, Y : Element_Type) return Boolean is (X = Y) with
        Annotate => (GNATprove, Container_Aggregates, "Equivalent_Elements");

   private
      type T_Content is array (Element_Type) of Boolean;
      type T is record
         Content : T_Content;
      end record;

      function Empty return T is
        ((Content => (others => False)));

      function Contains (X : T; E : Element_Type) return Boolean is
        (X.Content (E));
   end P3;

begin
   null;
end;
