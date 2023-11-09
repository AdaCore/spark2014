procedure Test_Sets with SPARK_Mode is

   --  OK

   package P1 is
      type Element_Type is new Integer;
      type T is private with
        Aggregate => (Empty       => Empty,
                      Add_Unnamed => Insert),
        Annotate => (GNATprove, Container_Aggregates, "Predefined_Sets"); --@CONTAINER_AGGR_ANNOTATION:PASS

      function Empty return T with
        Global => null,
        Import,
        Post => Length (Empty'Result) = 0
        and then (for all E in Element_Type => not Contains (Empty'Result, E));
      procedure Insert (X : in out T; E : Element_Type) with
        Global => null,
        Always_Terminates,
        Import,
        Post =>
	(if Contains (X, E)'Old then Length (X) = Length (X)'Old
	 else Length (X) = Length (X)'Old + 1)
        and then Contains (X, E)
        and then (for all F in Element_Type =>
                    (if Contains (X, F) then Contains (X'Old, F) or Eq_Elem (F, E)))
        and then (for all F in Element_Type =>
                    (if Contains (X'Old, F) then Contains (X, F)));

      function Contains (X : T; E : Element_Type) return Boolean with
        Annotate => (GNATprove, Container_Aggregates, "Contains"),
        Global => null,
        Import;

      function Length (X : T) return Natural with
        Annotate => (GNATprove, Container_Aggregates, "Length"),
        Global => null,
        Import;

      function Eq_Elem (X, Y : Element_Type) return Boolean with
        Annotate => (GNATprove, Container_Aggregates, "Equivalent_Elements"),
        Global => null,
        Import;

   private
      pragma SPARK_Mode (Off);
      type T is new Integer;
   end P1;

   --  Missing post on length on Empty

   package P2 is
      type Element_Type is new Integer;
      type T is private with
        Aggregate => (Empty       => Empty,
                      Add_Unnamed => Insert),
        Annotate => (GNATprove, Container_Aggregates, "Predefined_Sets"); --@CONTAINER_AGGR_ANNOTATION:FAIL

      function Empty return T with
        Global => null,
        Import,
        Post => (for all E in Element_Type => not Contains (Empty'Result, E));
      procedure Insert (X : in out T; E : Element_Type) with
        Global => null,
        Always_Terminates,
        Import,
        Post =>
	(if Contains (X, E)'Old then Length (X) = Length (X)'Old
	 else Length (X) = Length (X)'Old + 1)
        and then Contains (X, E)
        and then (for all F in Element_Type =>
                    (if Contains (X, F) then Contains (X'Old, F) or Eq_Elem (F, E)))
        and then (for all F in Element_Type =>
                    (if Contains (X'Old, F) then Contains (X, F)));

      function Contains (X : T; E : Element_Type) return Boolean with
        Annotate => (GNATprove, Container_Aggregates, "Contains"),
        Global => null,
        Import;

      function Length (X : T) return Natural with
        Annotate => (GNATprove, Container_Aggregates, "Length"),
        Global => null,
        Import;

      function Eq_Elem (X, Y : Element_Type) return Boolean with
        Annotate => (GNATprove, Container_Aggregates, "Equivalent_Elements"),
        Global => null,
        Import;

   private
      pragma SPARK_Mode (Off);
      type T is new Integer;
   end P2;

   --  Missing post on contains on Empty

   package P3 is
      type Element_Type is new Integer;
      type T is private with
        Aggregate => (Empty       => Empty,
                      Add_Unnamed => Insert),
        Annotate => (GNATprove, Container_Aggregates, "Predefined_Sets"); --@CONTAINER_AGGR_ANNOTATION:FAIL

      function Empty return T with
        Global => null,
        Import,
        Post => Length (Empty'Result) = 0;
      procedure Insert (X : in out T; E : Element_Type) with
        Global => null,
        Always_Terminates,
        Import,
        Post =>
	(if Contains (X, E)'Old then Length (X) = Length (X)'Old
	 else Length (X) = Length (X)'Old + 1)
        and then Contains (X, E)
        and then (for all F in Element_Type =>
                    (if Contains (X, F) then Contains (X'Old, F) or Eq_Elem (F, E)))
        and then (for all F in Element_Type =>
                    (if Contains (X'Old, F) then Contains (X, F)));

      function Contains (X : T; E : Element_Type) return Boolean with
        Annotate => (GNATprove, Container_Aggregates, "Contains"),
        Global => null,
        Import;

      function Length (X : T) return Natural with
        Annotate => (GNATprove, Container_Aggregates, "Length"),
        Global => null,
        Import;

      function Eq_Elem (X, Y : Element_Type) return Boolean with
        Annotate => (GNATprove, Container_Aggregates, "Equivalent_Elements"),
        Global => null,
        Import;

   private
      pragma SPARK_Mode (Off);
      type T is new Integer;
   end P3;

   --  Missing post on length on Insert

   package P4 is
      type Element_Type is new Integer;
      type T is private with
        Aggregate => (Empty       => Empty,
                      Add_Unnamed => Insert),
        Annotate => (GNATprove, Container_Aggregates, "Predefined_Sets"); --@CONTAINER_AGGR_ANNOTATION:FAIL

      function Empty return T with
        Global => null,
        Import,
        Post => Length (Empty'Result) = 0
        and then (for all E in Element_Type => not Contains (Empty'Result, E));
      procedure Insert (X : in out T; E : Element_Type) with
        Global => null,
        Always_Terminates,
        Import,
        Post => Contains (X, E)
        and then (for all F in Element_Type =>
                    (if Contains (X, F) then Contains (X'Old, F) or Eq_Elem (F, E)))
        and then (for all F in Element_Type =>
                    (if Contains (X'Old, F) then Contains (X, F)));

      function Contains (X : T; E : Element_Type) return Boolean with
        Annotate => (GNATprove, Container_Aggregates, "Contains"),
        Global => null,
        Import;

      function Length (X : T) return Natural with
        Annotate => (GNATprove, Container_Aggregates, "Length"),
        Global => null,
        Import;

      function Eq_Elem (X, Y : Element_Type) return Boolean with
        Annotate => (GNATprove, Container_Aggregates, "Equivalent_Elements"),
        Global => null,
        Import;

   private
      pragma SPARK_Mode (Off);
      type T is new Integer;
   end P4;

   --  Missing post on contains for added element on Insert

   package P5 is
      type Element_Type is new Integer;
      type T is private with
        Aggregate => (Empty       => Empty,
                      Add_Unnamed => Insert),
        Annotate => (GNATprove, Container_Aggregates, "Predefined_Sets"); --@CONTAINER_AGGR_ANNOTATION:FAIL

      function Empty return T with
        Global => null,
        Import,
        Post => Length (Empty'Result) = 0
        and then (for all E in Element_Type => not Contains (Empty'Result, E));
      procedure Insert (X : in out T; E : Element_Type) with
        Global => null,
        Always_Terminates,
        Import,
        Post =>
	(if Contains (X, E)'Old then Length (X) = Length (X)'Old
	 else Length (X) = Length (X)'Old + 1)
        and then (for all F in Element_Type =>
                    (if Contains (X, F) then Contains (X'Old, F) or Eq_Elem (F, E)))
        and then (for all F in Element_Type =>
                    (if Contains (X'Old, F) then Contains (X, F)));

      function Contains (X : T; E : Element_Type) return Boolean with
        Annotate => (GNATprove, Container_Aggregates, "Contains"),
        Global => null,
        Import;

      function Length (X : T) return Natural with
        Annotate => (GNATprove, Container_Aggregates, "Length"),
        Global => null,
        Import;

      function Eq_Elem (X, Y : Element_Type) return Boolean with
        Annotate => (GNATprove, Container_Aggregates, "Equivalent_Elements"),
        Global => null,
        Import;

   private
      pragma SPARK_Mode (Off);
      type T is new Integer;
   end P5;

   --  Missing post on contains for old elements on Insert

   package P6 is
      type Element_Type is new Integer;
      type T is private with
        Aggregate => (Empty       => Empty,
                      Add_Unnamed => Insert),
        Annotate => (GNATprove, Container_Aggregates, "Predefined_Sets"); --@CONTAINER_AGGR_ANNOTATION:FAIL

      function Empty return T with
        Global => null,
        Import,
        Post => Length (Empty'Result) = 0
        and then (for all E in Element_Type => not Contains (Empty'Result, E));
      procedure Insert (X : in out T; E : Element_Type) with
        Global => null,
        Always_Terminates,
        Import,
        Post =>
	(if Contains (X, E)'Old then Length (X) = Length (X)'Old
	 else Length (X) = Length (X)'Old + 1)
        and then Contains (X, E)
        and then (for all F in Element_Type =>
                    (if Contains (X, F) then Contains (X'Old, F) or Eq_Elem (F, E)));

      function Contains (X : T; E : Element_Type) return Boolean with
        Annotate => (GNATprove, Container_Aggregates, "Contains"),
        Global => null,
        Import;

      function Length (X : T) return Natural with
        Annotate => (GNATprove, Container_Aggregates, "Length"),
        Global => null,
        Import;

      function Eq_Elem (X, Y : Element_Type) return Boolean with
        Annotate => (GNATprove, Container_Aggregates, "Equivalent_Elements"),
        Global => null,
        Import;

   private
      pragma SPARK_Mode (Off);
      type T is new Integer;
   end P6;

   --  Missing post on contains for new elements on Insert

   package P7 is
      type Element_Type is new Integer;
      type T is private with
        Aggregate => (Empty       => Empty,
                      Add_Unnamed => Insert),
        Annotate => (GNATprove, Container_Aggregates, "Predefined_Sets"); --@CONTAINER_AGGR_ANNOTATION:FAIL

      function Empty return T with
        Global => null,
        Import,
        Post => Length (Empty'Result) = 0
        and then (for all E in Element_Type => not Contains (Empty'Result, E));
      procedure Insert (X : in out T; E : Element_Type) with
        Global => null,
        Always_Terminates,
        Import,
        Post =>
	(if Contains (X, E)'Old then Length (X) = Length (X)'Old
	 else Length (X) = Length (X)'Old + 1)
        and then (for all F in Element_Type =>
                    (if Contains (X, F) then Contains (X'Old, F) or Eq_Elem (F, E)));

      function Contains (X : T; E : Element_Type) return Boolean with
        Annotate => (GNATprove, Container_Aggregates, "Contains"),
        Global => null,
        Import;

      function Length (X : T) return Natural with
        Annotate => (GNATprove, Container_Aggregates, "Length"),
        Global => null,
        Import;

      function Eq_Elem (X, Y : Element_Type) return Boolean with
        Annotate => (GNATprove, Container_Aggregates, "Equivalent_Elements"),
        Global => null,
        Import;

   private
      pragma SPARK_Mode (Off);
      type T is new Integer;
   end P7;

   --  Incorrect precondition on Empty

   package P8 is
      type Element_Type is new Integer;
      type T is private with
        Aggregate => (Empty       => Empty,
                      Add_Unnamed => Insert),
        Annotate => (GNATprove, Container_Aggregates, "Predefined_Sets");

      function Pred return Boolean with
        Global => null,
        Import;

      function Empty return T with
        Pre => Pred, --@PRECONDITION:FAIL
        Global => null,
        Import,
        Post => Length (Empty'Result) = 0
        and then (for all E in Element_Type => not Contains (Empty'Result, E));
      procedure Insert (X : in out T; E : Element_Type) with
        Global => null,
        Always_Terminates,
        Import,
        Post =>
	(if Contains (X, E)'Old then Length (X) = Length (X)'Old
	 else Length (X) = Length (X)'Old + 1)
        and then Contains (X, E)
        and then (for all F in Element_Type =>
                    (if Contains (X, F) then Contains (X'Old, F) or Eq_Elem (F, E)))
        and then (for all F in Element_Type =>
                    (if Contains (X'Old, F) then Contains (X, F)));

      function Contains (X : T; E : Element_Type) return Boolean with
        Annotate => (GNATprove, Container_Aggregates, "Contains"),
        Global => null,
        Import;

      function Length (X : T) return Natural with
        Annotate => (GNATprove, Container_Aggregates, "Length"),
        Global => null,
        Import;

      function Eq_Elem (X, Y : Element_Type) return Boolean with
        Annotate => (GNATprove, Container_Aggregates, "Equivalent_Elements"),
        Global => null,
        Import;

   private
      pragma SPARK_Mode (Off);
      type T is new Integer;
   end P8;

   --  Incorrect precondition on Insert

   package P9 is
      type Element_Type is new Integer;
      type T is private with
        Aggregate => (Empty       => Empty,
                      Add_Unnamed => Insert),
        Annotate => (GNATprove, Container_Aggregates, "Predefined_Sets");

      function Pred (X : T; E : Element_Type) return Boolean with
        Global => null,
        Import;

      function Empty return T with
        Global => null,
        Import,
        Post => Length (Empty'Result) = 0
        and then (for all E in Element_Type => not Contains (Empty'Result, E));
      procedure Insert (X : in out T; E : Element_Type) with
        Pre => Pred (X, E), --@PRECONDITION:FAIL
        Global => null,
        Always_Terminates,
        Import,
        Post =>
	(if Contains (X, E)'Old then Length (X) = Length (X)'Old
	 else Length (X) = Length (X)'Old + 1)
        and then Contains (X, E)
        and then (for all F in Element_Type =>
                    (if Contains (X, F) then Contains (X'Old, F) or Eq_Elem (F, E)))
        and then (for all F in Element_Type =>
                    (if Contains (X'Old, F) then Contains (X, F)));

      function Contains (X : T; E : Element_Type) return Boolean with
        Annotate => (GNATprove, Container_Aggregates, "Contains"),
        Global => null,
        Import;

      function Length (X : T) return Natural with
        Annotate => (GNATprove, Container_Aggregates, "Length"),
        Global => null,
        Import;

      function Eq_Elem (X, Y : Element_Type) return Boolean with
        Annotate => (GNATprove, Container_Aggregates, "Equivalent_Elements"),
        Global => null,
        Import;

   private
      pragma SPARK_Mode (Off);
      type T is new Integer;
   end P9;

   --  Insert can be called on elements already in the set

   package P10 is
      type Element_Type is new Integer;
      type T is private with
        Aggregate => (Empty       => Empty,
                      Add_Unnamed => Insert),
        Annotate => (GNATprove, Container_Aggregates, "Predefined_Sets");

      function Empty return T with
        Global => null,
        Import,
        Post => Length (Empty'Result) = 0
        and then (for all E in Element_Type => not Contains (Empty'Result, E));
      procedure Insert (X : in out T; E : Element_Type) with
        Pre => not Contains (X, E), --@PRECONDITION:FAIL
        Global => null,
        Always_Terminates,
        Import,
        Post =>
	(if Contains (X, E)'Old then Length (X) = Length (X)'Old
	 else Length (X) = Length (X)'Old + 1)
        and then Contains (X, E)
        and then (for all F in Element_Type =>
                    (if Contains (X, F) then Contains (X'Old, F) or Eq_Elem (F, E)))
        and then (for all F in Element_Type =>
                    (if Contains (X'Old, F) then Contains (X, F)));

      function Contains (X : T; E : Element_Type) return Boolean with
        Annotate => (GNATprove, Container_Aggregates, "Contains"),
        Global => null,
        Import;

      function Length (X : T) return Natural with
        Annotate => (GNATprove, Container_Aggregates, "Length"),
        Global => null,
        Import;

      function Eq_Elem (X, Y : Element_Type) return Boolean with
        Annotate => (GNATprove, Container_Aggregates, "Equivalent_Elements"),
        Global => null,
        Import;

   private
      pragma SPARK_Mode (Off);
      type T is new Integer;
   end P10;

   --  Missing Post on Capacity on Empty

   package P11 is
      type Element_Type is new Integer;

      type T (Capacity : Natural) is private with
        Aggregate => (Empty       => Empty,
                      Add_Unnamed => Append),
        Annotate => (GNATprove, Container_Aggregates, "Predefined_Sets"); --@CONTAINER_AGGR_ANNOTATION:FAIL

      function Empty (X : Natural) return T with
        Global => null;
      procedure Append (X : in out T; E : Element_Type) with
        Global => null,
        Pre  => Length (X) < Capacity (X),
        Post => Contains (X, E)
        and then (for all F in Element_Type =>
                    Contains (X, F) = (Contains (X'Old, F) or F = E))
        and then (if Contains (X'Old, E) then Length (X) = Length (X'Old)
                  else Length (X) = Length (X'Old) + 1)
        and then Capacity (X) >= Capacity (X'Old),
        Always_Terminates,
        Import;

      function Length (X : T) return Natural with
        Global => null,
        Annotate => (GNATprove, Container_Aggregates, "Length");

      function Capacity (X : T) return Natural with
        Global => null,
        Import,
        Annotate => (GNATprove, Container_Aggregates, "Capacity");

      function Contains (X : T; E : Element_Type) return Boolean with
        Annotate => (GNATprove, Container_Aggregates, "Contains");

      function Eq_Element (X, Y : Element_Type) return Boolean is (X = Y) with
        Annotate => (GNATprove, Container_Aggregates, "Equivalent_Elements");

   private
      type T_Content is array (Positive range <>) of Element_Type with
        Relaxed_Initialization;

      type T (Capacity : Natural) is record
         Content : T_Content (1 .. Capacity);
         Top     : Natural;
      end record with
        Ghost_Predicate => Top <= Capacity
        and then (for all I in 1 .. Top => Content (I)'Initialized);

      function Contains (X : T; E : Element_Type) return Boolean is
        (for some I in 1 .. X.Top => X.Content (I) = E);
      function Length (X : T) return Natural is (X.Top);

      function Empty (X : Natural) return T is
        ((Capacity => X, Content => (others => <>), Top => 0));
   end P11;

   --  Missing Post on Capacity on Append

   package P12 is
      type Element_Type is new Integer;

      type T (Capacity : Natural) is private with
        Aggregate => (Empty       => Empty,
                      Add_Unnamed => Append),
        Annotate => (GNATprove, Container_Aggregates, "Predefined_Sets"); --@CONTAINER_AGGR_ANNOTATION:FAIL

      function Empty (X : Natural) return T with
        Import,
        Global => null,
        Post => Length (Empty'Result) = 0 and then Capacity (Empty'Result) >= X;
      procedure Append (X : in out T; E : Element_Type) with
        Global => null,
        Pre  => Length (X) < Capacity (X),
        Post => Contains (X, E)
        and then (for all F in Element_Type =>
                    Contains (X, F) = (Contains (X'Old, F) or F = E))
        and then (if Contains (X'Old, E) then Length (X) = Length (X'Old)
                  else Length (X) = Length (X'Old) + 1),
        Always_Terminates,
        Import;

      function Length (X : T) return Natural with
        Global => null,
        Annotate => (GNATprove, Container_Aggregates, "Length");

      function Capacity (X : T) return Natural with
        Global => null,
        Import,
        Annotate => (GNATprove, Container_Aggregates, "Capacity");

      function Contains (X : T; E : Element_Type) return Boolean with
        Annotate => (GNATprove, Container_Aggregates, "Contains");

      function Eq_Element (X, Y : Element_Type) return Boolean is (X = Y) with
        Annotate => (GNATprove, Container_Aggregates, "Equivalent_Elements");

   private
      type T_Content is array (Positive range <>) of Element_Type with
        Relaxed_Initialization;

      type T (Capacity : Natural) is record
         Content : T_Content (1 .. Capacity);
         Top     : Natural;
      end record with
        Ghost_Predicate => Top <= Capacity
        and then (for all I in 1 .. Top => Content (I)'Initialized);

      function Contains (X : T; E : Element_Type) return Boolean is
        (for some I in 1 .. X.Top => X.Content (I) = E);
      function Length (X : T) return Natural is (X.Top);

   end P12;

   --  Correct posts on Capacity

   package P13 is
      type Element_Type is new Integer;

      type T (Capacity : Natural) is private with
        Aggregate => (Empty       => Empty,
                      Add_Unnamed => Append),
        Annotate => (GNATprove, Container_Aggregates, "Predefined_Sets"); --@CONTAINER_AGGR_ANNOTATION:PASS

      function Empty (X : Natural) return T with
        Import,
        Global => null,
        Post => Length (Empty'Result) = 0 and then Capacity (Empty'Result) >= X;
      procedure Append (X : in out T; E : Element_Type) with
        Global => null,
        Pre  => Length (X) < Capacity (X),
        Post => Contains (X, E)
        and then (for all F in Element_Type =>
                    Contains (X, F) = (Contains (X'Old, F) or F = E))
        and then (if Contains (X'Old, E) then Length (X) = Length (X'Old)
                  else Length (X) = Length (X'Old) + 1)
        and then Capacity (X) >= Capacity (X'Old),
        Always_Terminates,
        Import;

      function Length (X : T) return Natural with
        Global => null,
        Annotate => (GNATprove, Container_Aggregates, "Length");

      function Capacity (X : T) return Natural with
        Global => null,
        Import,
        Annotate => (GNATprove, Container_Aggregates, "Capacity");

      function Contains (X : T; E : Element_Type) return Boolean with
        Annotate => (GNATprove, Container_Aggregates, "Contains");

      function Eq_Element (X, Y : Element_Type) return Boolean is (X = Y) with
        Annotate => (GNATprove, Container_Aggregates, "Equivalent_Elements");

   private
      type T_Content is array (Positive range <>) of Element_Type with
        Relaxed_Initialization;

      type T (Capacity : Natural) is record
         Content : T_Content (1 .. Capacity);
         Top     : Natural;
      end record with
        Ghost_Predicate => Top <= Capacity
        and then (for all I in 1 .. Top => Content (I)'Initialized);

      function Contains (X : T; E : Element_Type) return Boolean is
        (for some I in 1 .. X.Top => X.Content (I) = E);
      function Length (X : T) return Natural is (X.Top);
   end P13;

   --  No post needed on global Capacity

   package P14 is
      Max : constant Natural := 100;
      type Element_Type is new Integer;

      type T is private with
        Aggregate => (Empty       => Empty,
                      Add_Unnamed => Append),
        Annotate => (GNATprove, Container_Aggregates, "Predefined_Sets"); --@CONTAINER_AGGR_ANNOTATION:PASS

      Empty : constant T;
      procedure Append (X : in out T; E : Element_Type) with
        Global => null,
        Pre => Length (X) < Capacity,
        Post => Contains (X, E)
        and then (for all F in Element_Type =>
                    Contains (X, F) = (Contains (X'Old, F) or F = E))
        and then (if Contains (X'Old, E) then Length (X) = Length (X'Old)
                  else Length (X) = Length (X'Old) + 1),
        Always_Terminates,
        Import;

      function Length (X : T) return Natural with
        Global => null,
        Annotate => (GNATprove, Container_Aggregates, "Length");

      function Capacity return Natural with
        Global => null,
        Import,
        Annotate => (GNATprove, Container_Aggregates, "Capacity");

      function Contains (X : T; E : Element_Type) return Boolean with
        Annotate => (GNATprove, Container_Aggregates, "Contains");

      function Eq_Element (X, Y : Element_Type) return Boolean is (X = Y) with
        Annotate => (GNATprove, Container_Aggregates, "Equivalent_Elements");

   private
      type T_Content is array (Positive range 1 .. Max) of Element_Type with
        Relaxed_Initialization;

      type T is record
         Content : T_Content;
         Top     : Natural;
      end record with
        Ghost_Predicate => Top <= Max
        and then (for all I in 1 .. Top => Content (I)'Initialized);

      function Contains (X : T; E : Element_Type) return Boolean is
        (for some I in 1 .. X.Top => X.Content (I) = E);
      function Length (X : T) return Natural is (X.Top);

      Empty : constant T :=
        ((Content => (others => <>), Top => 0));
   end P14;
begin
   null;
end;
