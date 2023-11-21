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
begin
   null;
end;
