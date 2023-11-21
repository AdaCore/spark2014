procedure Test_Illegal_Glob with SPARK_Mode is

   --  Fourth param shall be an entity

   package P1 is
      type Element_Type is range 1 .. 100;
      type T is private with
        Aggregate => (Empty       => Empty,
                      Add_Unnamed => Insert);
      pragma Annotate (GNATprove, Container_Aggregates, "Predefined_Sets", 12);

      function Empty return T;
      procedure Insert (X : in out T; E : Element_Type) with
        Global => null,
        Always_Terminates,
        Import;

   private
      type T_Content is array (Element_Type) of Boolean;
      type T is record
         Content : T_Content;
      end record;

      function Empty return T is
        ((Content => (others => False)));
   end P1;

   --  Third param shall be a string litteral

   package P2 is
      type Element_Type is range 1 .. 100;
      type T is private with
        Aggregate => (Empty       => Empty,
                      Add_Unnamed => Insert),
        Annotate => (GNATprove, Container_Aggregates, 12);

      function Empty return T;
      procedure Insert (X : in out T; E : Element_Type) with
        Global => null,
        Always_Terminates,
        Import;

   private
      type T_Content is array (Element_Type) of Boolean;
      type T is record
         Content : T_Content;
      end record;

      function Empty return T is
        ((Content => (others => False)));
   end P2;

   --  Third param shall be an expected string litteral

   package P3 is
      type Element_Type is range 1 .. 100;
      type T is private with
        Aggregate => (Empty       => Empty,
                      Add_Unnamed => Insert),
        Annotate => (GNATprove, Container_Aggregates, "foo");

      function Empty return T;
      procedure Insert (X : in out T; E : Element_Type) with
        Global => null,
        Always_Terminates,
        Import;

      function Contains (X : T; E : Element_Type) return Boolean with
        Annotate => (GNATprove, Container_Aggregates, "bar");

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

   --  Type entity shall have a private declaration

   package P4 is
      type Element_Type is range 1 .. 100;
      type T_Content is array (Element_Type) of Boolean;
      type T is record
         Content : T_Content;
      end record with
        Aggregate => (Empty       => Empty,
                      Add_Unnamed => Insert),
        Annotate => (GNATprove, Container_Aggregates, "Predefined_Sets");

      function Empty return T is
        ((Content => (others => False)));
      procedure Insert (X : in out T; E : Element_Type) with
        Global => null,
        Always_Terminates,
        Import;
   end P4;

   --  Type entity shall have a private declaration

   package P5 is
      package Nested is
         type Element_Type is range 1 .. 100;
         type T is private;

         function Empty return T;

      private
         type T_Content is array (Element_Type) of Boolean;
         type T is record
            Content : T_Content;
         end record;

         function Empty return T is
           ((Content => (others => False)));
      end Nested;
      use Nested;

      type T2 is new T with
        Aggregate => (Empty       => Empty,
                      Add_Unnamed => Insert),
        Annotate => (GNATprove, Container_Aggregates, "Predefined_Sets");

      procedure Insert (X : in out T2; E : Element_Type) with
        Global => null,
        Always_Terminates,
        Import;
      function Empty return T2 is (T2 (Nested.Empty));
   end P5;

   --  Type entity shall have a Aggregate aspect

   package P6 is
      type Element_Type is range 1 .. 100;
      type T is private with
        Annotate => (GNATprove, Container_Aggregates, "Predefined_Sets");

      function Empty return T;
      procedure Insert (X : in out T; E : Element_Type) with
        Global => null,
        Always_Terminates,
        Import;

   private
      type T_Content is array (Element_Type) of Boolean;
      type T is record
         Content : T_Content;
      end record;

      function Empty return T is
        ((Content => (others => False)));
   end P6;

begin
   null;
end Test_Illegal_Glob;
