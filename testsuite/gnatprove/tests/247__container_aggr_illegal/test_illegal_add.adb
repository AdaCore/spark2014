
procedure Test_Illegal_Add with SPARK_Mode is

   --  Add procedure which might not terminate

   package P1 is
      type Element_Type is range 1 .. 100;
      type T is private with
        Aggregate => (Empty       => Empty,
                      Add_Unnamed => Insert),
        Annotate => (GNATprove, Container_Aggregates, "Predefined_Sets");

      function Empty return T;
      procedure Insert (X : in out T; E : Element_Type) with
        Global => null,
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
   end P1;

   --  Add procedure which might raise exceptions

   package P2 is
      type Element_Type is range 1 .. 100;
      type T is private with
        Aggregate => (Empty       => Empty,
                      Add_Unnamed => Insert),
        Annotate => (GNATprove, Container_Aggregates, "Predefined_Sets");

      function Empty return T;
      procedure Insert (X : in out T; E : Element_Type) with
        Global => null,
        Always_Terminates => True,
        Exceptional_Cases => (others => True),
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

   --  Add procedure accesses global data

   package P3 is
      type Element_Type is range 1 .. 100;
      type T is private with
        Aggregate => (Empty       => Empty,
                      Add_Unnamed => Insert),
        Annotate => (GNATprove, Container_Aggregates, "Predefined_Sets");

      V : Integer;

      function Empty return T;
      procedure Insert (X : in out T; E : Element_Type) with
        Global => V,
        Always_Terminates => True,
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

   --  Add procedure writes global data

   package P4 is
      type Element_Type is range 1 .. 100;
      type T is private with
        Aggregate => (Empty       => Empty,
                      Add_Unnamed => Insert),
        Annotate => (GNATprove, Container_Aggregates, "Predefined_Sets");

      V : Integer;

      function Empty return T;
      procedure Insert (X : in out T; E : Element_Type) with
        Global => (In_Out => V),
        Always_Terminates => True,
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
   end P4;

begin
   null;
end;
