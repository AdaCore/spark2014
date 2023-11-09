procedure Test_Partial_Maps with SPARK_Mode is

   --  OK

   package P1 is
      type Key_Type is new Integer;
      type Element_Type is private;
      type T is private with
        Aggregate => (Empty       => Empty,
                      Add_Named => Insert),
        Annotate => (GNATprove, Container_Aggregates, "Predefined_Maps"); --@CONTAINER_AGGR_ANNOTATION:PASS

      function Empty return T with
        Global => null,
        Import,
        Post => Length (Empty'Result) = 0
        and then (for all K in Key_Type => not Has_Key (Empty'Result, K));
      procedure Insert (X : in out T; K : Key_Type; E : Element_Type) with
        Global => null,
        Pre => not Has_Key (X, K),
        Post => Length (X) - 1 = Length (X)'Old
        and then Has_Key (X, K)
        and then (for all L in Key_Type =>
                    (if Has_Key (X, L) then Has_Key (X'Old, L) or Eq_Key (L, K)))
        and then (for all F in Key_Type =>
                    (if Has_Key (X'Old, F) then Has_Key (X, F)))
        and then Get (X, K) = E
        and then (for all F in Key_Type =>
                    (if Has_Key (X'Old, F) then Get (X, F) = Get (X'Old, F))),
        Always_Terminates,
        Import;

      function Has_Key (X : T; K : Key_Type) return Boolean with
        Annotate => (GNATprove, Container_Aggregates, "Has_Key"),
        Global => null,
        Import;

      function Get (X : T; K : Key_Type) return Element_Type with
        Pre => Has_Key (X, K),
        Annotate => (GNATprove, Container_Aggregates, "Get"),
        Global => null,
        Import;

      function Eq_Key (X, Y : Key_Type) return Boolean with
        Annotate => (GNATprove, Container_Aggregates, "Equivalent_Keys"),
        Global => null,
        Import;

      function Length (X : T) return Natural with
        Annotate => (GNATprove, Container_Aggregates, "Length"),
        Global => null,
        Import;

   private
      pragma SPARK_Mode (Off);
      type Element_Type is new Integer;
      type T is new Integer;
   end P1;

   --  Missing post on length on Empty

   package P2 is
      type Key_Type is new Integer;
      type Element_Type is private;
      type T is private with
        Aggregate => (Empty       => Empty,
                      Add_Named => Insert),
        Annotate => (GNATprove, Container_Aggregates, "Predefined_Maps"); --@CONTAINER_AGGR_ANNOTATION:FAIL

      function Empty return T with
        Global => null,
        Import,
        Post => (for all K in Key_Type => not Has_Key (Empty'Result, K));
      procedure Insert (X : in out T; K : Key_Type; E : Element_Type) with
        Global => null,
        Pre => not Has_Key (X, K),
        Post => Length (X) - 1 = Length (X)'Old
        and then Has_Key (X, K)
        and then (for all L in Key_Type =>
                    (if Has_Key (X, L) then Has_Key (X'Old, L) or Eq_Key (L, K)))
        and then (for all F in Key_Type =>
                    (if Has_Key (X'Old, F) then Has_Key (X, F)))
        and then Get (X, K) = E
        and then (for all F in Key_Type =>
                    (if Has_Key (X'Old, F) then Get (X, F) = Get (X'Old, F))),
        Always_Terminates,
        Import;

      function Has_Key (X : T; K : Key_Type) return Boolean with
        Annotate => (GNATprove, Container_Aggregates, "Has_Key"),
        Global => null,
        Import;

      function Get (X : T; K : Key_Type) return Element_Type with
        Pre => Has_Key (X, K),
        Annotate => (GNATprove, Container_Aggregates, "Get"),
        Global => null,
        Import;

      function Eq_Key (X, Y : Key_Type) return Boolean with
        Annotate => (GNATprove, Container_Aggregates, "Equivalent_Keys"),
        Global => null,
        Import;

      function Length (X : T) return Natural with
        Annotate => (GNATprove, Container_Aggregates, "Length"),
        Global => null,
        Import;

   private
      pragma SPARK_Mode (Off);
      type Element_Type is new Integer;
      type T is new Integer;
   end P2;

   --  Missing post on has_key on Empty

   package P3 is
      type Key_Type is new Integer;
      type Element_Type is private;
      type T is private with
        Aggregate => (Empty       => Empty,
                      Add_Named => Insert),
        Annotate => (GNATprove, Container_Aggregates, "Predefined_Maps"); --@CONTAINER_AGGR_ANNOTATION:FAIL

      function Empty return T with
        Global => null,
        Import,
        Post => Length (Empty'Result) = 0;
      procedure Insert (X : in out T; K : Key_Type; E : Element_Type) with
        Global => null,
        Pre => not Has_Key (X, K),
        Post => Length (X) - 1 = Length (X)'Old
        and then Has_Key (X, K)
        and then (for all L in Key_Type =>
                    (if Has_Key (X, L) then Has_Key (X'Old, L) or Eq_Key (L, K)))
        and then (for all F in Key_Type =>
                    (if Has_Key (X'Old, F) then Has_Key (X, F)))
        and then Get (X, K) = E
        and then (for all F in Key_Type =>
                    (if Has_Key (X'Old, F) then Get (X, F) = Get (X'Old, F))),
        Always_Terminates,
        Import;

      function Has_Key (X : T; K : Key_Type) return Boolean with
        Annotate => (GNATprove, Container_Aggregates, "Has_Key"),
        Global => null,
        Import;

      function Get (X : T; K : Key_Type) return Element_Type with
        Pre => Has_Key (X, K),
        Annotate => (GNATprove, Container_Aggregates, "Get"),
        Global => null,
        Import;

      function Eq_Key (X, Y : Key_Type) return Boolean with
        Annotate => (GNATprove, Container_Aggregates, "Equivalent_Keys"),
        Global => null,
        Import;

      function Length (X : T) return Natural with
        Annotate => (GNATprove, Container_Aggregates, "Length"),
        Global => null,
        Import;

   private
      pragma SPARK_Mode (Off);
      type Element_Type is new Integer;
      type T is new Integer;
   end P3;

   --  Missing post on length on Insert

   package P4 is
      type Key_Type is new Integer;
      type Element_Type is private;
      type T is private with
        Aggregate => (Empty       => Empty,
                      Add_Named => Insert),
        Annotate => (GNATprove, Container_Aggregates, "Predefined_Maps"); --@CONTAINER_AGGR_ANNOTATION:FAIL

      function Empty return T with
        Global => null,
        Import,
        Post => Length (Empty'Result) = 0
        and then (for all K in Key_Type => not Has_Key (Empty'Result, K));
      procedure Insert (X : in out T; K : Key_Type; E : Element_Type) with
        Global => null,
        Pre => not Has_Key (X, K),
        Post => Has_Key (X, K)
        and then (for all L in Key_Type =>
                    (if Has_Key (X, L) then Has_Key (X'Old, L) or Eq_Key (L, K)))
        and then (for all F in Key_Type =>
                    (if Has_Key (X'Old, F) then Has_Key (X, F)))
        and then Get (X, K) = E
        and then (for all F in Key_Type =>
                    (if Has_Key (X'Old, F) then Get (X, F) = Get (X'Old, F))),
        Always_Terminates,
        Import;

      function Has_Key (X : T; K : Key_Type) return Boolean with
        Annotate => (GNATprove, Container_Aggregates, "Has_Key"),
        Global => null,
        Import;

      function Get (X : T; K : Key_Type) return Element_Type with
        Pre => Has_Key (X, K),
        Annotate => (GNATprove, Container_Aggregates, "Get"),
        Global => null,
        Import;

      function Eq_Key (X, Y : Key_Type) return Boolean with
        Annotate => (GNATprove, Container_Aggregates, "Equivalent_Keys"),
        Global => null,
        Import;

      function Length (X : T) return Natural with
        Annotate => (GNATprove, Container_Aggregates, "Length"),
        Global => null,
        Import;

   private
      pragma SPARK_Mode (Off);
      type Element_Type is new Integer;
      type T is new Integer;
   end P4;

   --  Missing post on has_key for added key on Insert

   package P5 is
      type Key_Type is new Integer;
      type Element_Type is private;
      type T is private with
        Aggregate => (Empty       => Empty,
                      Add_Named => Insert),
        Annotate => (GNATprove, Container_Aggregates, "Predefined_Maps"); --@CONTAINER_AGGR_ANNOTATION:FAIL

      function Empty return T with
        Global => null,
        Import,
        Post => Length (Empty'Result) = 0
        and then (for all K in Key_Type => not Has_Key (Empty'Result, K));
      procedure Insert (X : in out T; K : Key_Type; E : Element_Type) with
        Global => null,
        Pre => not Has_Key (X, K),
        Post => Length (X) - 1 = Length (X)'Old
        and then (for all L in Key_Type =>
                    (if Has_Key (X, L) then Has_Key (X'Old, L) or Eq_Key (L, K)))
        and then (for all F in Key_Type =>
                    (if Has_Key (X'Old, F) then Has_Key (X, F)))
        and then Get (X, K) = E
        and then (for all F in Key_Type =>
                    (if Has_Key (X'Old, F) then Get (X, F) = Get (X'Old, F))),
        Always_Terminates,
        Import;

      function Has_Key (X : T; K : Key_Type) return Boolean with
        Annotate => (GNATprove, Container_Aggregates, "Has_Key"),
        Global => null,
        Import;

      function Get (X : T; K : Key_Type) return Element_Type with
        Pre => Has_Key (X, K),
        Annotate => (GNATprove, Container_Aggregates, "Get"),
        Global => null,
        Import;

      function Eq_Key (X, Y : Key_Type) return Boolean with
        Annotate => (GNATprove, Container_Aggregates, "Equivalent_Keys"),
        Global => null,
        Import;

      function Length (X : T) return Natural with
        Annotate => (GNATprove, Container_Aggregates, "Length"),
        Global => null,
        Import;

   private
      pragma SPARK_Mode (Off);
      type Element_Type is new Integer;
      type T is new Integer;
   end P5;

   --  Missing post on has_key for old keys on Insert

   package P6 is
      type Key_Type is new Integer;
      type Element_Type is private;
      type T is private with
        Aggregate => (Empty       => Empty,
                      Add_Named => Insert),
        Annotate => (GNATprove, Container_Aggregates, "Predefined_Maps"); --@CONTAINER_AGGR_ANNOTATION:FAIL

      function Empty return T with
        Global => null,
        Import,
        Post => Length (Empty'Result) = 0
        and then (for all K in Key_Type => not Has_Key (Empty'Result, K));
      procedure Insert (X : in out T; K : Key_Type; E : Element_Type) with
        Global => null,
        Pre => not Has_Key (X, K),
        Post => Length (X) - 1 = Length (X)'Old
        and then Has_Key (X, K)
        and then (for all L in Key_Type =>
                    (if Has_Key (X, L) then Has_Key (X'Old, L) or Eq_Key (L, K)))
        and then Get (X, K) = E
        and then (for all F in Key_Type =>
                    (if Has_Key (X'Old, F) then Get (X, F) = Get (X'Old, F))),
        Always_Terminates,
        Import;

      function Has_Key (X : T; K : Key_Type) return Boolean with
        Annotate => (GNATprove, Container_Aggregates, "Has_Key"),
        Global => null,
        Import;

      function Get (X : T; K : Key_Type) return Element_Type with
        Pre => Has_Key (X, K),
        Annotate => (GNATprove, Container_Aggregates, "Get"),
        Global => null,
        Import;

      function Eq_Key (X, Y : Key_Type) return Boolean with
        Annotate => (GNATprove, Container_Aggregates, "Equivalent_Keys"),
        Global => null,
        Import;

      function Length (X : T) return Natural with
        Annotate => (GNATprove, Container_Aggregates, "Length"),
        Global => null,
        Import;

   private
      pragma SPARK_Mode (Off);
      type Element_Type is new Integer;
      type T is new Integer;
   end P6;

   --  Missing post on has_key for new keys on Insert

   package P7 is
      type Key_Type is new Integer;
      type Element_Type is private;
      type T is private with
        Aggregate => (Empty       => Empty,
                      Add_Named => Insert),
        Annotate => (GNATprove, Container_Aggregates, "Predefined_Maps"); --@CONTAINER_AGGR_ANNOTATION:FAIL

      function Empty return T with
        Global => null,
        Import,
        Post => Length (Empty'Result) = 0
        and then (for all K in Key_Type => not Has_Key (Empty'Result, K));
      procedure Insert (X : in out T; K : Key_Type; E : Element_Type) with
        Global => null,
        Pre => not Has_Key (X, K),
        Post => Length (X) - 1 = Length (X)'Old
        and then Has_Key (X, K)
        and then (for all F in Key_Type =>
                    (if Has_Key (X'Old, F) then Has_Key (X, F)))
        and then Get (X, K) = E
        and then (for all F in Key_Type =>
                    (if Has_Key (X'Old, F) then Get (X, F) = Get (X'Old, F))),
        Always_Terminates,
        Import;

      function Has_Key (X : T; K : Key_Type) return Boolean with
        Annotate => (GNATprove, Container_Aggregates, "Has_Key"),
        Global => null,
        Import;

      function Get (X : T; K : Key_Type) return Element_Type with
        Pre => Has_Key (X, K),
        Annotate => (GNATprove, Container_Aggregates, "Get"),
        Global => null,
        Import;

      function Eq_Key (X, Y : Key_Type) return Boolean with
        Annotate => (GNATprove, Container_Aggregates, "Equivalent_Keys"),
        Global => null,
        Import;

      function Length (X : T) return Natural with
        Annotate => (GNATprove, Container_Aggregates, "Length"),
        Global => null,
        Import;

   private
      pragma SPARK_Mode (Off);
      type Element_Type is new Integer;
      type T is new Integer;
   end P7;

   --  Missing post on get for added key on Insert

   package P8 is
      type Key_Type is new Integer;
      type Element_Type is private;
      type T is private with
        Aggregate => (Empty       => Empty,
                      Add_Named => Insert),
        Annotate => (GNATprove, Container_Aggregates, "Predefined_Maps"); --@CONTAINER_AGGR_ANNOTATION:FAIL

      function Empty return T with
        Global => null,
        Import,
        Post => Length (Empty'Result) = 0
        and then (for all K in Key_Type => not Has_Key (Empty'Result, K));
      procedure Insert (X : in out T; K : Key_Type; E : Element_Type) with
        Global => null,
        Pre => not Has_Key (X, K),
        Post => Length (X) - 1 = Length (X)'Old
        and then Has_Key (X, K)
        and then (for all L in Key_Type =>
                    (if Has_Key (X, L) then Has_Key (X'Old, L) or Eq_Key (L, K)))
        and then (for all F in Key_Type =>
                    (if Has_Key (X'Old, F) then Has_Key (X, F)))
        and then (for all F in Key_Type =>
                    (if Has_Key (X'Old, F) then Get (X, F) = Get (X'Old, F))),
        Always_Terminates,
        Import;

      function Has_Key (X : T; K : Key_Type) return Boolean with
        Annotate => (GNATprove, Container_Aggregates, "Has_Key"),
        Global => null,
        Import;

      function Get (X : T; K : Key_Type) return Element_Type with
        Pre => Has_Key (X, K),
        Annotate => (GNATprove, Container_Aggregates, "Get"),
        Global => null,
        Import;

      function Eq_Key (X, Y : Key_Type) return Boolean with
        Annotate => (GNATprove, Container_Aggregates, "Equivalent_Keys"),
        Global => null,
        Import;

      function Length (X : T) return Natural with
        Annotate => (GNATprove, Container_Aggregates, "Length"),
        Global => null,
        Import;

   private
      pragma SPARK_Mode (Off);
      type Element_Type is new Integer;
      type T is new Integer;
   end P8;

   --  Missing post on get for old key on Insert

   package P9 is
      type Key_Type is new Integer;
      type Element_Type is private;
      type T is private with
        Aggregate => (Empty       => Empty,
                      Add_Named => Insert),
        Annotate => (GNATprove, Container_Aggregates, "Predefined_Maps"); --@CONTAINER_AGGR_ANNOTATION:FAIL

      function Empty return T with
        Global => null,
        Import,
        Post => Length (Empty'Result) = 0
        and then (for all K in Key_Type => not Has_Key (Empty'Result, K));
      procedure Insert (X : in out T; K : Key_Type; E : Element_Type) with
        Global => null,
        Pre => not Has_Key (X, K),
        Post => Length (X) - 1 = Length (X)'Old
        and then Has_Key (X, K)
        and then (for all L in Key_Type =>
                    (if Has_Key (X, L) then Has_Key (X'Old, L) or Eq_Key (L, K)))
        and then (for all F in Key_Type =>
                    (if Has_Key (X'Old, F) then Has_Key (X, F)))
        and then Get (X, K) = E,
        Always_Terminates,
        Import;

      function Has_Key (X : T; K : Key_Type) return Boolean with
        Annotate => (GNATprove, Container_Aggregates, "Has_Key"),
        Global => null,
        Import;

      function Get (X : T; K : Key_Type) return Element_Type with
        Pre => Has_Key (X, K),
        Annotate => (GNATprove, Container_Aggregates, "Get"),
        Global => null,
        Import;

      function Eq_Key (X, Y : Key_Type) return Boolean with
        Annotate => (GNATprove, Container_Aggregates, "Equivalent_Keys"),
        Global => null,
        Import;

      function Length (X : T) return Natural with
        Annotate => (GNATprove, Container_Aggregates, "Length"),
        Global => null,
        Import;

   private
      pragma SPARK_Mode (Off);
      type Element_Type is new Integer;
      type T is new Integer;
   end P9;

   --  Incorrect precondition on Empty

   package P10 is
      type Key_Type is new Integer;
      type Element_Type is private;
      type T is private with
        Aggregate => (Empty       => Empty,
                      Add_Named => Insert),
        Annotate => (GNATprove, Container_Aggregates, "Predefined_Maps");

      function Pred return Boolean with
        Global => null,
        Import;

      function Empty return T with
        Global => null,
        Import,
        Pre => Pred, --@PRECONDITION:FAIL
        Post => Length (Empty'Result) = 0
        and then (for all K in Key_Type => not Has_Key (Empty'Result, K));
      procedure Insert (X : in out T; K : Key_Type; E : Element_Type) with
        Global => null,
        Pre => not Has_Key (X, K),
        Post => Length (X) - 1 = Length (X)'Old
        and then Has_Key (X, K)
        and then (for all L in Key_Type =>
                    (if Has_Key (X, L) then Has_Key (X'Old, L) or Eq_Key (L, K)))
        and then (for all F in Key_Type =>
                    (if Has_Key (X'Old, F) then Has_Key (X, F)))
        and then Get (X, K) = E
        and then (for all F in Key_Type =>
                    (if Has_Key (X'Old, F) then Get (X, F) = Get (X'Old, F))),
        Always_Terminates,
        Import;

      function Has_Key (X : T; K : Key_Type) return Boolean with
        Annotate => (GNATprove, Container_Aggregates, "Has_Key"),
        Global => null,
        Import;

      function Get (X : T; K : Key_Type) return Element_Type with
        Pre => Has_Key (X, K),
        Annotate => (GNATprove, Container_Aggregates, "Get"),
        Global => null,
        Import;

      function Eq_Key (X, Y : Key_Type) return Boolean with
        Annotate => (GNATprove, Container_Aggregates, "Equivalent_Keys"),
        Global => null,
        Import;

      function Length (X : T) return Natural with
        Annotate => (GNATprove, Container_Aggregates, "Length"),
        Global => null,
        Import;

   private
      pragma SPARK_Mode (Off);
      type Element_Type is new Integer;
      type T is new Integer;
   end P10;

   --  Incorrect precondition on Insert

   package P11 is
      type Key_Type is new Integer;
      type Element_Type is private;
      type T is private with
        Aggregate => (Empty       => Empty,
                      Add_Named => Insert),
        Annotate => (GNATprove, Container_Aggregates, "Predefined_Maps");

      function Pred (X : T; K : Key_Type; E : Element_Type) return Boolean with
        Global => null,
        Import;

      function Empty return T with
        Global => null,
        Import,
        Post => Length (Empty'Result) = 0
        and then (for all K in Key_Type => not Has_Key (Empty'Result, K));
      procedure Insert (X : in out T; K : Key_Type; E : Element_Type) with
        Global => null,
        Pre => not Has_Key (X, K) and then Pred (X, K, E), --@PRECONDITION:FAIL
        Post => Length (X) - 1 = Length (X)'Old
        and then Has_Key (X, K)
        and then (for all L in Key_Type =>
                    (if Has_Key (X, L) then Has_Key (X'Old, L) or Eq_Key (L, K)))
        and then (for all F in Key_Type =>
                    (if Has_Key (X'Old, F) then Has_Key (X, F)))
        and then Get (X, K) = E
        and then (for all F in Key_Type =>
                    (if Has_Key (X'Old, F) then Get (X, F) = Get (X'Old, F))),
        Always_Terminates,
        Import;

      function Has_Key (X : T; K : Key_Type) return Boolean with
        Annotate => (GNATprove, Container_Aggregates, "Has_Key"),
        Global => null,
        Import;

      function Get (X : T; K : Key_Type) return Element_Type with
        Pre => Has_Key (X, K),
        Annotate => (GNATprove, Container_Aggregates, "Get"),
        Global => null,
        Import;

      function Eq_Key (X, Y : Key_Type) return Boolean with
        Annotate => (GNATprove, Container_Aggregates, "Equivalent_Keys"),
        Global => null,
        Import;

      function Length (X : T) return Natural with
        Annotate => (GNATprove, Container_Aggregates, "Length"),
        Global => null,
        Import;

   private
      pragma SPARK_Mode (Off);
      type Element_Type is new Integer;
      type T is new Integer;
   end P11;

   --  Missing Post on Capacity on Empty

   package P12 is
      type Key_Type is new Integer;
      type Element_Type is new Integer;

      type T (Capacity : Natural) is private with
        Aggregate => (Empty       => Empty,
                      Add_Named => Append),
        Annotate => (GNATprove, Container_Aggregates, "Predefined_Maps"); --@CONTAINER_AGGR_ANNOTATION:FAIL

      function Empty (X : Natural) return T with
        Global => null,
        Post => Length (Empty'Result) = 0,
        Import;
      procedure Append (X : in out T; K : Key_Type; E : Element_Type) with
        Global => null,
        Pre  => Length (X) < Capacity (X) and then not Has_Key (X, K),
        Post => Has_Key (X, K)
        and then Get (X, K) = E
        and then (for all L in Key_Type =>
                    Has_Key (X, L) = (Has_Key (X'Old, L) or L = K))
        and then (for all L in Key_Type =>
                    (if Has_Key (X'Old, L) then Get (X, L) = Get (X'Old, L)))
        and then Length (X) = Length (X'Old) + 1
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

      function Has_Key (X : T; K : Key_Type) return Boolean with
        Annotate => (GNATprove, Container_Aggregates, "Has_Key");

      function Get (X : T; K : Key_Type) return Element_Type with
        Pre => Has_Key (X, K),
        Annotate => (GNATprove, Container_Aggregates, "Get");

      function Eq_Keys (X, Y : Key_Type) return Boolean is (X = Y) with
        Annotate => (GNATprove, Container_Aggregates, "Equivalent_Keys");

   private
      type Key_Elem is record
         K : Key_Type;
         E : Element_Type;
      end record;
      type T_Content is array (Positive range <>) of Key_Elem with
        Relaxed_Initialization;

      type T (Capacity : Natural) is record
         Content : T_Content (1 .. Capacity);
         Top     : Natural;
      end record with
        Ghost_Predicate => Top <= Capacity
        and then (for all I in 1 .. Top => Content (I)'Initialized);

      function Has_Key (X : T; K : Key_Type) return Boolean is
        (for some I in 1 .. X.Top => X.Content (I).K = K);
      function Length (X : T) return Natural is (X.Top);

      function Get (X : T_Content; K : Key_Type; Top : Natural) return Element_Type with
        Pre => X'First = 1 and then Top in X'Range
        and then (for all I in 1 .. Top => X (I)'Initialized)
        and then (for some I in 1 .. Top => X (I).K = K),
        Subprogram_Variant => (Decreases => Top);

      function Get (X : T_Content; K : Key_Type; Top : Natural) return Element_Type is
        (if X (Top).K = K then X (Top).E else Get (X, K, Top - 1));

      function Get (X : T; K : Key_Type) return Element_Type is
        (Get (X.Content, K, X.Top));
   end P12;

   --  Missing Post on Capacity on Add

   package P13 is
      type Key_Type is new Integer;
      type Element_Type is new Integer;

      type T (Capacity : Natural) is private with
        Aggregate => (Empty       => Empty,
                      Add_Named => Append),
        Annotate => (GNATprove, Container_Aggregates, "Predefined_Maps"); --@CONTAINER_AGGR_ANNOTATION:FAIL

      function Empty (X : Natural) return T with
        Global => null,
        Post => Length (Empty'Result) = 0 and then Capacity (Empty'Result) >= X,
        Import;
      procedure Append (X : in out T; K : Key_Type; E : Element_Type) with
        Global => null,
        Pre  => Length (X) < Capacity (X) and then not Has_Key (X, K),
        Post => Has_Key (X, K)
        and then Get (X, K) = E
        and then (for all L in Key_Type =>
                    Has_Key (X, L) = (Has_Key (X'Old, L) or L = K))
        and then (for all L in Key_Type =>
                    (if Has_Key (X'Old, L) then Get (X, L) = Get (X'Old, L)))
        and then Length (X) = Length (X'Old) + 1,
        Always_Terminates,
        Import;

      function Length (X : T) return Natural with
        Global => null,
        Annotate => (GNATprove, Container_Aggregates, "Length");

      function Capacity (X : T) return Natural with
        Global => null,
        Import,
        Annotate => (GNATprove, Container_Aggregates, "Capacity");

      function Has_Key (X : T; K : Key_Type) return Boolean with
        Annotate => (GNATprove, Container_Aggregates, "Has_Key");

      function Get (X : T; K : Key_Type) return Element_Type with
        Pre => Has_Key (X, K),
        Annotate => (GNATprove, Container_Aggregates, "Get");

      function Eq_Keys (X, Y : Key_Type) return Boolean is (X = Y) with
        Annotate => (GNATprove, Container_Aggregates, "Equivalent_Keys");

   private
      type Key_Elem is record
         K : Key_Type;
         E : Element_Type;
      end record;
      type T_Content is array (Positive range <>) of Key_Elem with
        Relaxed_Initialization;

      type T (Capacity : Natural) is record
         Content : T_Content (1 .. Capacity);
         Top     : Natural;
      end record with
        Ghost_Predicate => Top <= Capacity
        and then (for all I in 1 .. Top => Content (I)'Initialized);

      function Has_Key (X : T; K : Key_Type) return Boolean is
        (for some I in 1 .. X.Top => X.Content (I).K = K);
      function Length (X : T) return Natural is (X.Top);

      function Get (X : T_Content; K : Key_Type; Top : Natural) return Element_Type with
        Pre => X'First = 1 and then Top in X'Range
        and then (for all I in 1 .. Top => X (I)'Initialized)
        and then (for some I in 1 .. Top => X (I).K = K),
        Subprogram_Variant => (Decreases => Top);

      function Get (X : T_Content; K : Key_Type; Top : Natural) return Element_Type is
        (if X (Top).K = K then X (Top).E else Get (X, K, Top - 1));

      function Get (X : T; K : Key_Type) return Element_Type is
        (Get (X.Content, K, X.Top));
   end P13;

   --  Correct posts on Capacity

   package P14 is
      type Key_Type is new Integer;
      type Element_Type is new Integer;

      type T (Capacity : Natural) is private with
        Aggregate => (Empty       => Empty,
                      Add_Named => Append),
        Annotate => (GNATprove, Container_Aggregates, "Predefined_Maps"); --@CONTAINER_AGGR_ANNOTATION:PASS

      function Empty (X : Natural) return T with
        Global => null,
        Post => Length (Empty'Result) = 0 and then Capacity (Empty'Result) >= X,
        Import;
      procedure Append (X : in out T; K : Key_Type; E : Element_Type) with
        Global => null,
        Pre  => Length (X) < Capacity (X) and then not Has_Key (X, K),
        Post => Has_Key (X, K)
        and then Get (X, K) = E
        and then (for all L in Key_Type =>
                    Has_Key (X, L) = (Has_Key (X'Old, L) or L = K))
        and then (for all L in Key_Type =>
                    (if Has_Key (X'Old, L) then Get (X, L) = Get (X'Old, L)))
        and then Length (X) = Length (X'Old) + 1
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

      function Has_Key (X : T; K : Key_Type) return Boolean with
        Annotate => (GNATprove, Container_Aggregates, "Has_Key");

      function Get (X : T; K : Key_Type) return Element_Type with
        Pre => Has_Key (X, K),
        Annotate => (GNATprove, Container_Aggregates, "Get");

      function Eq_Keys (X, Y : Key_Type) return Boolean is (X = Y) with
        Annotate => (GNATprove, Container_Aggregates, "Equivalent_Keys");

   private
      type Key_Elem is record
         K : Key_Type;
         E : Element_Type;
      end record;
      type T_Content is array (Positive range <>) of Key_Elem with
        Relaxed_Initialization;

      type T (Capacity : Natural) is record
         Content : T_Content (1 .. Capacity);
         Top     : Natural;
      end record with
        Ghost_Predicate => Top <= Capacity
        and then (for all I in 1 .. Top => Content (I)'Initialized);

      function Has_Key (X : T; K : Key_Type) return Boolean is
        (for some I in 1 .. X.Top => X.Content (I).K = K);
      function Length (X : T) return Natural is (X.Top);

      function Get (X : T_Content; K : Key_Type; Top : Natural) return Element_Type with
        Pre => X'First = 1 and then Top in X'Range
        and then (for all I in 1 .. Top => X (I)'Initialized)
        and then (for some I in 1 .. Top => X (I).K = K),
        Subprogram_Variant => (Decreases => Top);

      function Get (X : T_Content; K : Key_Type; Top : Natural) return Element_Type is
        (if X (Top).K = K then X (Top).E else Get (X, K, Top - 1));

      function Get (X : T; K : Key_Type) return Element_Type is
        (Get (X.Content, K, X.Top));
   end P14;

   --  No post needed for global Capacity

   package P15 is
      Max : constant Natural := 100;
      type Key_Type is new Integer;
      type Element_Type is new Integer;

      type T is private with
        Aggregate => (Empty       => Empty,
                      Add_Named => Append),
        Annotate => (GNATprove, Container_Aggregates, "Predefined_Maps"); --@CONTAINER_AGGR_ANNOTATION:PASS

      Empty : constant T;
      procedure Append (X : in out T; K : Key_Type; E : Element_Type) with
        Global => null,
        Pre  => Length (X) < Capacity and then not Has_Key (X, K),
        Post => Has_Key (X, K)
        and then Get (X, K) = E
        and then (for all L in Key_Type =>
                    Has_Key (X, L) = (Has_Key (X'Old, L) or L = K))
        and then (for all L in Key_Type =>
                    (if Has_Key (X'Old, L) then Get (X, L) = Get (X'Old, L)))
        and then Length (X) = Length (X'Old) + 1,
        Always_Terminates,
        Import;

      function Length (X : T) return Natural with
        Global => null,
        Annotate => (GNATprove, Container_Aggregates, "Length");

      function Capacity return Natural with
        Global => null,
        Import,
        Annotate => (GNATprove, Container_Aggregates, "Capacity");

      function Has_Key (X : T; K : Key_Type) return Boolean with
        Annotate => (GNATprove, Container_Aggregates, "Has_Key");

      function Get (X : T; K : Key_Type) return Element_Type with
        Pre => Has_Key (X, K),
        Annotate => (GNATprove, Container_Aggregates, "Get");

      function Eq_Keys (X, Y : Key_Type) return Boolean is (X = Y) with
        Annotate => (GNATprove, Container_Aggregates, "Equivalent_Keys");

   private
      type Key_Elem is record
         K : Key_Type;
         E : Element_Type;
      end record;
      type T_Content is array (Positive range 1 .. Max) of Key_Elem with
        Relaxed_Initialization;

      type T is record
         Content : T_Content;
         Top     : Natural;
      end record with
        Ghost_Predicate => Top <= Max
        and then (for all I in 1 .. Top => Content (I)'Initialized);

      function Has_Key (X : T; K : Key_Type) return Boolean is
        (for some I in 1 .. X.Top => X.Content (I).K = K);
      function Length (X : T) return Natural is (X.Top);

      function Get (X : T_Content; K : Key_Type; Top : Natural) return Element_Type with
        Pre => Top in X'Range
        and then (for all I in 1 .. Top => X (I)'Initialized)
        and then (for some I in 1 .. Top => X (I).K = K),
        Subprogram_Variant => (Decreases => Top);

      function Get (X : T_Content; K : Key_Type; Top : Natural) return Element_Type is
        (if X (Top).K = K then X (Top).E else Get (X, K, Top - 1));

      function Get (X : T; K : Key_Type) return Element_Type is
        (Get (X.Content, K, X.Top));

      Empty : constant T :=
        (Content => (others => <>), Top => 0);
   end P15;
begin
   null;
end;
