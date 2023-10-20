procedure Test_Illegal_Aggregates with SPARK_Mode is

   --  Bad container aggregate, no Container_Aggregates annotation

   procedure P1 is
      package Sets is
         type Element_Type is range 1 .. 100;
         type T is private with
           Aggregate => (Empty       => Empty,
                         Add_Unnamed => Insert);

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
      end Sets;
      use Sets;

      S : Sets.T := [1, 2, 3];
   begin
      null;
   end P1;

   --  Bad container aggregate, Empty is not in SPARK

   procedure P2 is
      package Sets is
         type Element_Type is range 1 .. 100;
         type T is private with
           Aggregate => (Empty       => Empty,
                         Add_Unnamed => Insert),
           Annotate => (GNATprove, Container_Aggregates, "Predefined_Sets");

         function Empty return T with
           Global => null,
           Import,
           SPARK_Mode => Off;
         procedure Insert (X : in out T; E : Element_Type) with
           Global => null,
           Always_Terminates,
           Import;

         function Contains (X : T; E : Element_Type) return Boolean with
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

         function Contains (X : T; E : Element_Type) return Boolean is
           (X.Content (E));
      end Sets;
      use Sets;

      S : Sets.T := [1, 2, 3];
   begin
      null;
   end P2;

   --  Bad container aggregate, Insert is not in SPARK

   procedure P3 is
      package Sets is
         type Element_Type is range 1 .. 100;
         type T is private with
           Aggregate => (Empty       => Empty,
                         Add_Unnamed => Insert),
           Annotate => (GNATprove, Container_Aggregates, "Predefined_Sets");

         function Empty return T;
         procedure Insert (X : in out T; E : Element_Type) with
           SPARK_Mode => Off,
           Global => null,
           Always_Terminates,
           Import;

         function Contains (X : T; E : Element_Type) return Boolean with
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

         function Contains (X : T; E : Element_Type) return Boolean is
           (X.Content (E));
      end Sets;
      use Sets;

      S : Sets.T := [1, 2, 3];
   begin
      null;
   end P3;

   --  OK container aggregate

   procedure P4 is
      package Sets is
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

         function Contains (X : T; E : Element_Type) return Boolean is
           (X.Content (E));
      end Sets;
      use Sets;

      S : Sets.T := [1, 2, 3];
   begin
      null;
   end P4;

begin
   null;
end Test_Illegal_Aggregates;
