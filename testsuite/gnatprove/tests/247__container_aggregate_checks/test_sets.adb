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
        Post => Length (X) - 1 <= Length (X)'Old
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
        Post => Length (X) - 1 <= Length (X)'Old
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
        Post => Length (X) - 1 <= Length (X)'Old
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
        Post => Length (X) - 1 <= Length (X)'Old
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
        Post => Length (X) - 1 <= Length (X)'Old
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
        Post => Length (X) - 1 <= Length (X)'Old
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
        Post => Length (X) - 1 <= Length (X)'Old
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
        Post => Length (X) - 1 <= Length (X)'Old
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
        Post => Length (X) - 1 <= Length (X)'Old
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
begin
   null;
end;
