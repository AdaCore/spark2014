procedure Test_Total_Maps with SPARK_Mode is

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
        Post => (for all K in Key_Type => Get (Empty'Result, K) = Default_Value);
      procedure Insert (X : in out T; K : Key_Type; E : Element_Type) with
        Global => null,
        Always_Terminates,
        Import,
        Pre  => Get (X, K) = Default_Value,
        Post => Get (X, K) = E
        and then (for all F in Key_Type =>
                    (if not Eq_Key (F, K) then Get (X, F) = Get (X'Old, F)));

      function Default_Value return Element_Type with
        Annotate => (GNATprove, Container_Aggregates, "Default_Item"),
        Global => null,
        Import;

      function Get (X : T; K : Key_Type) return Element_Type with
        Annotate => (GNATprove, Container_Aggregates, "Get"),
        Global => null,
        Import;

      function Eq_Key (X, Y : Key_Type) return Boolean with
        Annotate => (GNATprove, Container_Aggregates, "Equivalent_Keys"),
        Global => null,
        Import;

   private
      pragma SPARK_Mode (Off);
      type Element_Type is new Integer;
      type T is new Integer;
   end P1;

   --  Missing post on Get on Empty

   package P2 is
      type Key_Type is new Integer;
      type Element_Type is private;
      type T is private with
        Aggregate => (Empty       => Empty,
                      Add_Named => Insert),
        Annotate => (GNATprove, Container_Aggregates, "Predefined_Maps"); --@CONTAINER_AGGR_ANNOTATION:FAIL

      function Empty return T with
        Global => null,
        Import;
      procedure Insert (X : in out T; K : Key_Type; E : Element_Type) with
        Global => null,
        Always_Terminates,
        Import,
        Pre  => Get (X, K) = Default_Value,
        Post => Get (X, K) = E
        and then (for all F in Key_Type =>
                    (if not Eq_Key (F, K) then Get (X, F) = Get (X'Old, F)));

      function Default_Value return Element_Type with
        Annotate => (GNATprove, Container_Aggregates, "Default_Item"),
        Global => null,
        Import;

      function Get (X : T; K : Key_Type) return Element_Type with
        Annotate => (GNATprove, Container_Aggregates, "Get"),
        Global => null,
        Import;

      function Eq_Key (X, Y : Key_Type) return Boolean with
        Annotate => (GNATprove, Container_Aggregates, "Equivalent_Keys"),
        Global => null,
        Import;

   private
      pragma SPARK_Mode (Off);
      type Element_Type is new Integer;
      type T is new Integer;
   end P2;

   --  Missing post on Get on added key on Insert

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
        Post => (for all K in Key_Type => Get (Empty'Result, K) = Default_Value);
      procedure Insert (X : in out T; K : Key_Type; E : Element_Type) with
        Global => null,
        Always_Terminates,
        Import,
        Pre  => Get (X, K) = Default_Value,
        Post => (for all F in Key_Type =>
                    (if not Eq_Key (F, K) then Get (X, F) = Get (X'Old, F)));

      function Default_Value return Element_Type with
        Annotate => (GNATprove, Container_Aggregates, "Default_Item"),
        Global => null,
        Import;

      function Get (X : T; K : Key_Type) return Element_Type with
        Annotate => (GNATprove, Container_Aggregates, "Get"),
        Global => null,
        Import;

      function Eq_Key (X, Y : Key_Type) return Boolean with
        Annotate => (GNATprove, Container_Aggregates, "Equivalent_Keys"),
        Global => null,
        Import;

   private
      pragma SPARK_Mode (Off);
      type Element_Type is new Integer;
      type T is new Integer;
   end P3;

   --  Missing post on Get on other keys on Insert

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
        Post => (for all K in Key_Type => Get (Empty'Result, K) = Default_Value);
      procedure Insert (X : in out T; K : Key_Type; E : Element_Type) with
        Global => null,
        Always_Terminates,
        Import,
        Pre  => Get (X, K) = Default_Value,
        Post => Get (X, K) = E;

      function Default_Value return Element_Type with
        Annotate => (GNATprove, Container_Aggregates, "Default_Item"),
        Global => null,
        Import;

      function Get (X : T; K : Key_Type) return Element_Type with
        Annotate => (GNATprove, Container_Aggregates, "Get"),
        Global => null,
        Import;

      function Eq_Key (X, Y : Key_Type) return Boolean with
        Annotate => (GNATprove, Container_Aggregates, "Equivalent_Keys"),
        Global => null,
        Import;

   private
      pragma SPARK_Mode (Off);
      type Element_Type is new Integer;
      type T is new Integer;
   end P4;

   --  Incorrect precondition on Empty

   package P5 is
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
        Pre => Pred, --@PRECONDITION:FAIL
        Global => null,
        Import,
        Post => (for all K in Key_Type => Get (Empty'Result, K) = Default_Value);
      procedure Insert (X : in out T; K : Key_Type; E : Element_Type) with
        Global => null,
        Always_Terminates,
        Import,
        Pre  => Get (X, K) = Default_Value,
        Post => Get (X, K) = E
        and then (for all F in Key_Type =>
                    (if not Eq_Key (F, K) then Get (X, F) = Get (X'Old, F)));

      function Default_Value return Element_Type with
        Annotate => (GNATprove, Container_Aggregates, "Default_Item"),
        Global => null,
        Import;

      function Get (X : T; K : Key_Type) return Element_Type with
        Annotate => (GNATprove, Container_Aggregates, "Get"),
        Global => null,
        Import;

      function Eq_Key (X, Y : Key_Type) return Boolean with
        Annotate => (GNATprove, Container_Aggregates, "Equivalent_Keys"),
        Global => null,
        Import;

   private
      pragma SPARK_Mode (Off);
      type Element_Type is new Integer;
      type T is new Integer;
   end P5;

   --  Incorrect precondition on Insert

   package P6 is
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
        Post => (for all K in Key_Type => Get (Empty'Result, K) = Default_Value);
      procedure Insert (X : in out T; K : Key_Type; E : Element_Type) with
        Global => null,
        Always_Terminates,
        Import,
        Pre  => Get (X, K) = Default_Value and then Pred (X, K, E), --@PRECONDITION:FAIL
        Post => Get (X, K) = E
        and then (for all F in Key_Type =>
                    (if not Eq_Key (F, K) then Get (X, F) = Get (X'Old, F)));

      function Default_Value return Element_Type with
        Annotate => (GNATprove, Container_Aggregates, "Default_Item"),
        Global => null,
        Import;

      function Get (X : T; K : Key_Type) return Element_Type with
        Annotate => (GNATprove, Container_Aggregates, "Get"),
        Global => null,
        Import;

      function Eq_Key (X, Y : Key_Type) return Boolean with
        Annotate => (GNATprove, Container_Aggregates, "Equivalent_Keys"),
        Global => null,
        Import;

   private
      pragma SPARK_Mode (Off);
      type Element_Type is new Integer;
      type T is new Integer;
   end P6;
begin
   null;
end;
