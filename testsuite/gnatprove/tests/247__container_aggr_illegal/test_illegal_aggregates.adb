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

   --  Indexed container aggregate

   procedure P4 is


      package Seqs is
	 type Index_Type is new Integer range 1 .. 100;
	 subtype Ext_Index is Index_Type'Base range 0 .. 100;

	 type Element_Type is new Integer;

	 type T is private with
	   Aggregate => (Empty          => Empty,
			 New_Indexed    => New_Vector,
			 Assign_Indexed => Assign_Element,
			 Add_Unnamed    => Append),
	   Annotate => (GNATprove, Container_Aggregates, "Predefined_Sequences");

	 function Empty return T with
	   Import,
	   Global => null;

	 function First return Ext_Index is (1) with
	   Annotate => (GNATprove, Container_Aggregates, "First");

	 function Last (V : T) return Ext_Index with
	   Annotate => (GNATprove, Container_Aggregates, "Last");

	 function All_Init (X : T; Up : Ext_Index) return Boolean with
	   Ghost,
	   Pre => Up <= Last (X);

	 function All_Init (X : T) return Boolean is
	    (All_Init (X, Last (X))) with Ghost;

	    function Get (V : T; I : Index_Type) return Element_Type with
	      Pre => I <= Last (V) and then All_Init (V, I),
	      Annotate => (GNATprove, Container_Aggregates, "Get");

	    function New_Vector (First, Last : Index_Type) return T with
	      Import,
	      Global => null,
	      Pre => First = Index_Type'First;

	    procedure Assign_Element (V     : in out T;
				      Index : Index_Type;
				      Item  : Element_Type)
	      with
	      Global => null,
	      Always_Terminates,
	      Import,
	      Pre  => Index <= Last (V) and then All_Init (V, Index - 1),
	      Post => All_Init (V, Index);

	    procedure Append (V    : in out T;
			      Item : Element_Type)
	      with
	      Global => null,
	      Always_Terminates,
	      Import,
	      Pre => All_Init (V),
	      Post => All_Init (V);

      private
	 type T_Content is array (Index_Type) of Element_Type with
	   Relaxed_Initialization;
	 type T is record
	    Content : T_Content;
	    Top     : Ext_Index;
	 end record;

	 function Last (V : T) return Ext_Index is (V.Top);

	 function All_Init (X : T; Up : Ext_Index) return Boolean is
	    (for all I in 1 .. Up => X.Content (I)'Initialized);

	    function Get (V : T; I : Index_Type) return Element_Type is
	       (V.Content (I));
      end Seqs;
      use Seqs;

      X : Seqs.T := [1 => 1, 2 .. 5 => 8];

   begin
      null;
   end P4;

   --  OK container aggregate

   procedure P5 is
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
   end P5;

begin
   null;
end Test_Illegal_Aggregates;
