procedure Test_Capacity with SPARK_Mode is
   function Short_Index return Boolean with
     Global => null,
     Import;
   function Id (X : Integer) return Integer is (X);

   package Nested is
      Max : constant Natural := Id (10);
      subtype Small_Nat is Natural range 0 .. Max;

      Max_Index : constant Natural := (if Short_Index then 5 else 15);
   end Nested;
   use Nested;

   package Sets_With_Specific_Capacity is
      type Element_Type is new Integer;

      type T (Capacity : Natural) is private with
        Aggregate => (Empty       => Empty,
                      Add_Unnamed => Append),
        Annotate => (GNATprove, Container_Aggregates, "Predefined_Sets");

      function Empty (X : Small_Nat) return T with
        Global => null;
      procedure Append (X : in out T; E : Element_Type) with
        Global => null,
        Pre  => Length (X) < X.Capacity,
        Post => Contains (X, E)
        and then (for all F in Element_Type =>
                    Contains (X, F) = (Contains (X'Old, F) or F = E))
        and then (if Contains (X'Old, E) then Length (X) = Length (X'Old)
                  else Length (X) = Length (X'Old) + 1),
        Always_Terminates;

      function Length (X : T) return Natural with
        Global => null,
        Annotate => (GNATprove, Container_Aggregates, "Length");

      function Capacity (X : T) return Natural is (X.Capacity) with
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

      function Empty (X : Small_Nat) return T is
        ((Capacity => X, Content => (others => <>), Top => 0));
   end Sets_With_Specific_Capacity;

   package body Sets_With_Specific_Capacity is
      procedure Append (X : in out T; E : Element_Type) is
      begin
         if (for some I in 1 .. X.Top => X.Content (I) = E) then
            return;
         end if;

         X.Content (X.Top + 1) := E;
         X.Top := X.Top + 1;
      end Append;
   end Sets_With_Specific_Capacity;

   package Sets_With_Global_Capacity is
      type Element_Type is new Integer;

      type T is private with
        Aggregate => (Empty       => Empty,
                      Add_Unnamed => Append),
        Annotate => (GNATprove, Container_Aggregates, "Predefined_Sets");

      function Empty return T;
      procedure Append (X : in out T; E : Element_Type) with
        Global => null,
        Pre => Length (X) < Max,
        Post => Contains (X, E)
        and then (for all F in Element_Type =>
                    Contains (X, F) = (Contains (X'Old, F) or F = E))
        and then (if Contains (X'Old, E) then Length (X) = Length (X'Old)
                  else Length (X) = Length (X'Old) + 1),
        Always_Terminates;

      function Length (X : T) return Natural with
        Global => null,
        Annotate => (GNATprove, Container_Aggregates, "Length");

      function Capacity return Natural is (Max) with
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

      function Empty return T is
        ((Content => (others => <>), Top => 0));
   end Sets_With_Global_Capacity;

   package body Sets_With_Global_Capacity is
      procedure Append (X : in out T; E : Element_Type) is
      begin
         if (for some I in 1 .. X.Top => X.Content (I) = E) then
            return;
         end if;

         X.Content (X.Top + 1) := E;
         X.Top := X.Top + 1;
      end Append;
   end Sets_With_Global_Capacity;

   package Partial_Maps_With_Specific_Capacity is
      type Key_Type is new Integer;
      type Element_Type is new Integer;

      type T (Capacity : Natural) is private with
        Aggregate => (Empty       => Empty,
                      Add_Named => Append),
        Annotate => (GNATprove, Container_Aggregates, "Predefined_Maps");

      function Empty (X : Small_Nat) return T with
        Global => null;
      procedure Append (X : in out T; K : Key_Type; E : Element_Type) with
        Global => null,
        Pre  => Length (X) < X.Capacity and then not Has_Key (X, K),
        Post => Has_Key (X, K)
        and then Get (X, K) = E
        and then (for all L in Key_Type =>
                    Has_Key (X, L) = (Has_Key (X'Old, L) or L = K))
        and then (for all L in Key_Type =>
                    (if Has_Key (X'Old, L) then Get (X, L) = Get (X'Old, L)))
        and then Length (X) = Length (X'Old) + 1,
        Always_Terminates;

      function Length (X : T) return Natural with
        Global => null,
        Annotate => (GNATprove, Container_Aggregates, "Length");

      function Capacity (X : T) return Natural is (X.Capacity) with
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

      function Empty (X : Small_Nat) return T is
        ((Capacity => X, Content => (others => <>), Top => 0));
   end Partial_Maps_With_Specific_Capacity;

   package body Partial_Maps_With_Specific_Capacity is

      procedure Lemma_Get_Eq (X, Y : T_Content; Top : Natural) with
        Ghost,
        Pre => X'First = 1 and then Y'First = 1
        and then Top <= X'Last and then Top <= Y'Last
        and then (for all I in 1 .. Top => X (I)'Initialized and Y (I)'Initialized)
        and then (for all I in 1 .. Top => X (I) = Y (I)),
        Post => (for all K in Key_Type =>
                   (if (for some I in 1 .. Top => X (I).K = K)
                    then Get (X, K, Top) = Get (Y, K, Top))),
        Subprogram_Variant => (Decreases => Top);

      procedure Lemma_Get_Eq (X, Y : T_Content; Top : Natural) is
      begin
         if Top > 0 then
            Lemma_Get_Eq (X, Y, Top - 1);
         end if;
      end Lemma_Get_Eq;

      procedure Append (X : in out T; K : Key_Type; E : Element_Type) is
         X_Old : constant T := X with Ghost;
      begin
         X.Content (X.Top + 1) := (K, E);
         X.Top := X.Top + 1;
         Lemma_Get_Eq (X_Old.Content, X.Content, X.Top - 1);
      end Append;
   end Partial_Maps_With_Specific_Capacity;

   package Partial_Maps_With_Global_Capacity is
      type Key_Type is new Integer;
      type Element_Type is new Integer;

      type T is private with
        Aggregate => (Empty       => Empty,
                      Add_Named => Append),
        Annotate => (GNATprove, Container_Aggregates, "Predefined_Maps");

      function Empty return T;
      procedure Append (X : in out T; K : Key_Type; E : Element_Type) with
        Global => null,
        Pre  => Length (X) < Max and then not Has_Key (X, K),
        Post => Has_Key (X, K)
        and then Get (X, K) = E
        and then (for all L in Key_Type =>
                    Has_Key (X, L) = (Has_Key (X'Old, L) or L = K))
        and then (for all L in Key_Type =>
                    (if Has_Key (X'Old, L) then Get (X, L) = Get (X'Old, L)))
        and then Length (X) = Length (X'Old) + 1,
        Always_Terminates;

      function Length (X : T) return Natural with
        Global => null,
        Annotate => (GNATprove, Container_Aggregates, "Length");

      function Capacity return Natural is (Max) with
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
        Ghost_Predicate => Top <= Capacity
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

      function Empty return T is
        (Content => (others => <>), Top => 0);
   end Partial_Maps_With_Global_Capacity;

   package body Partial_Maps_With_Global_Capacity is

      procedure Lemma_Get_Eq (X, Y : T_Content; Top : Natural) with
        Ghost,
        Pre => Top <= X'Last and then Top <= Y'Last
        and then (for all I in 1 .. Top => X (I)'Initialized and Y (I)'Initialized)
        and then (for all I in 1 .. Top => X (I) = Y (I)),
        Post => (for all K in Key_Type =>
                   (if (for some I in 1 .. Top => X (I).K = K)
                    then Get (X, K, Top) = Get (Y, K, Top))),
        Subprogram_Variant => (Decreases => Top);

      procedure Lemma_Get_Eq (X, Y : T_Content; Top : Natural) is
      begin
         if Top > 0 then
            Lemma_Get_Eq (X, Y, Top - 1);
         end if;
      end Lemma_Get_Eq;

      procedure Append (X : in out T; K : Key_Type; E : Element_Type) is
         X_Old : constant T := X with Ghost;
      begin
         X.Content (X.Top + 1) := (K, E);
         X.Top := X.Top + 1;
         Lemma_Get_Eq (X_Old.Content, X.Content, X.Top - 1);
      end Append;
   end Partial_Maps_With_Global_Capacity;

   package Sequences_With_Specific_Capacity is
      subtype Index_Type is Natural range 1 .. Max_Index;
      subtype Ext_Index_Type is Index_Type'Base range 0 .. Index_Type'Last;
      type Element_Type is new Integer;

      type T (Capacity : Natural) is private with
        Aggregate => (Empty       => Empty,
                      Add_Unnamed => Append),
        Annotate => (GNATprove, Container_Aggregates, "Predefined_Sequences");

      function Empty (X : Small_Nat) return T with
        Global => null;
      procedure Append (X : in out T; E : Element_Type) with
        Global => null,
        Pre  => Integer (Last (X)) < X.Capacity and then Last (X) < Max_Index,
        Post => Last (X) = Last (X'Old) + 1
        and then Get (X, Last (X)) = E
        and then (for all I in 1 .. Last (X) - 1 =>
                    Get (X, I) = Get (X'Old, I)),
        Always_Terminates;

      function Capacity (X : T) return Natural is (X.Capacity) with
        Annotate => (GNATprove, Container_Aggregates, "Capacity");

      function First return Ext_Index_Type is (1) with
        Annotate => (GNATprove, Container_Aggregates, "First");

      function Last (X : T) return Ext_Index_Type with
        Annotate => (GNATprove, Container_Aggregates, "Last");

      function Get (X : T; I : Index_Type) return Element_Type with
        Pre => I <= Last (X),
        Annotate => (GNATprove, Container_Aggregates, "Get");

   private
      type T_Content is array (Positive range <>) of Element_Type with
        Relaxed_Initialization;

      Max_Capacity : constant Natural := Natural (Index_Type'Last);

      type T (Capacity : Natural) is record
         Content : T_Content (1 .. Capacity);
         Top     : Natural;
      end record with
        Ghost_Predicate => Capacity <= Max_Capacity
        and then Top <= Capacity
        and then (for all I in 1 .. Top => Content (I)'Initialized);

      function Last (X : T) return Ext_Index_Type is (Ext_Index_Type (X.Top));

      function Get (X : T; I : Index_Type) return Element_Type is
        (X.Content (Positive (I)));

      function Empty (X : Small_Nat) return T is
        ((Capacity => Natural'Min (Max_Capacity, X), Content => (others => <>), Top => 0));
   end Sequences_With_Specific_Capacity;

   package body Sequences_With_Specific_Capacity is
      procedure Append (X : in out T; E : Element_Type) is
      begin
         X.Content (X.Top + 1) := E;
         X.Top := X.Top + 1;
      end Append;
   end Sequences_With_Specific_Capacity;

   package Sequences_With_Global_Capacity is
      subtype Index_Type is Natural range 1 .. Max_Index;
      subtype Ext_Index_Type is Index_Type'Base range 0 .. Index_Type'Last;
      type Element_Type is new Integer;

      type T is private with
        Aggregate => (Empty       => Empty,
                      Add_Unnamed => Append),
        Annotate => (GNATprove, Container_Aggregates, "Predefined_Sequences");

      function Empty return T;
      procedure Append (X : in out T; E : Element_Type) with
        Global => null,
        Pre  => Integer (Last (X)) < Capacity and then Last (X) < Max_Index,
        Post => Last (X) = Last (X'Old) + 1
        and then Get (X, Last (X)) = E
        and then (for all I in 1 .. Last (X) - 1 =>
                    Get (X, I) = Get (X'Old, I)),
        Always_Terminates;

      function Capacity return Natural with
        Annotate => (GNATprove, Container_Aggregates, "Capacity");

      function First return Ext_Index_Type is (1) with
        Annotate => (GNATprove, Container_Aggregates, "First");

      function Last (X : T) return Ext_Index_Type with
        Annotate => (GNATprove, Container_Aggregates, "Last");

      function Get (X : T; I : Index_Type) return Element_Type with
        Pre => I <= Last (X),
        Annotate => (GNATprove, Container_Aggregates, "Get");

   private
      type T_Content is array (Positive range 1 .. Max) of Element_Type with
        Relaxed_Initialization;

      Max_Capacity : constant Natural := Natural (Index_Type'Last);

      type T is record
         Content : T_Content;
         Top     : Natural;
      end record with
        Ghost_Predicate => Top <= Max
        and then Top <= Max_Capacity
        and then (for all I in 1 .. Top => Content (I)'Initialized);

      function Last (X : T) return Ext_Index_Type is (Ext_Index_Type (X.Top));

      function Get (X : T; I : Index_Type) return Element_Type is
        (X.Content (Positive (I)));

      function Empty return T is ((Content => (others => <>), Top => 0));

      function Capacity return Natural is (Max);
   end Sequences_With_Global_Capacity;

   package body Sequences_With_Global_Capacity is
      procedure Append (X : in out T; E : Element_Type) is
      begin
         X.Content (X.Top + 1) := E;
         X.Top := X.Top + 1;
      end Append;
   end Sequences_With_Global_Capacity;

   procedure Test_Sets_With_Specific_Capacity with Global => null;

   procedure Test_Sets_With_Specific_Capacity is
      use Sets_With_Specific_Capacity;
      X : T := [1, 2, 3, 4, 5, 6, 7, 8, 9];
   begin
      pragma Assert (Capacity (X) >= 9);
   end Test_Sets_With_Specific_Capacity;

   procedure Test_Bad_Sets_With_Specific_Capacity with Global => null;

   procedure Test_Bad_Sets_With_Specific_Capacity is
      use Sets_With_Specific_Capacity;
      X : T := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]; -- @PRECONDITION:FAIL
   begin
      null;
   end Test_Bad_Sets_With_Specific_Capacity;

   procedure Test_Sets_With_Global_Capacity with Global => null;

   procedure Test_Sets_With_Global_Capacity is
      use Sets_With_Global_Capacity;
      X : T := [1, 2, 3, 4, 5, 6, 7, 8, 9];
   begin
      null;
   end Test_Sets_With_Global_Capacity;

   procedure Test_Bad_Sets_With_Global_Capacity with Global => null;

   procedure Test_Bad_Sets_With_Global_Capacity is
      use Sets_With_Global_Capacity;
      X : T := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]; -- @PRECONDITION:FAIL
   begin
      null;
   end Test_Bad_Sets_With_Global_Capacity;

   procedure Test_Maps_With_Specific_Capacity with Global => null;

   procedure Test_Maps_With_Specific_Capacity is
      use Partial_Maps_With_Specific_Capacity;
      X : T := [1 => 0, 2 => 0, 3 => 0, 4 => 0, 5 => 0, 6 => 0, 7 => 0, 8 => 0, 9 => 0];
   begin
      pragma Assert (Capacity (X) >= 9);
   end Test_Maps_With_Specific_Capacity;

   procedure Test_Bad_Maps_With_Specific_Capacity with Global => null;

   procedure Test_Bad_Maps_With_Specific_Capacity is
      use Partial_Maps_With_Specific_Capacity;
      X : T := [1 => 0, 2 => 0, 3 => 0, 4 => 0, 5 => 0, 6 => 0, 7 => 0, 8 => 0, 9 => 0, 10 => 0, 11 => 0]; -- @PRECONDITION:FAIL
   begin
      null;
   end Test_Bad_Maps_With_Specific_Capacity;

   procedure Test_Maps_With_Global_Capacity with Global => null;

   procedure Test_Maps_With_Global_Capacity is
      use Partial_Maps_With_Global_Capacity;
      X : T := [1 => 0, 2 => 0, 3 => 0, 4 => 0, 5 => 0, 6 => 0, 7 => 0, 8 => 0, 9 => 0];
   begin
      null;
   end Test_Maps_With_Global_Capacity;

   procedure Test_Bad_Maps_With_Global_Capacity with Global => null;

   procedure Test_Bad_Maps_With_Global_Capacity is
      use Partial_Maps_With_Global_Capacity;
      X : T := [1 => 0, 2 => 0, 3 => 0, 4 => 0, 5 => 0, 6 => 0, 7 => 0, 8 => 0, 9 => 0, 10 => 0, 11 => 0]; -- @PRECONDITION:FAIL
   begin
      null;
   end Test_Bad_Maps_With_Global_Capacity;

   procedure Test_Sequences_With_Specific_Capacity with
     Global => null,
     Pre => not Short_Index;

   procedure Test_Sequences_With_Specific_Capacity is
      use Sequences_With_Specific_Capacity;
      X : T := [1, 2, 3, 4, 5, 6, 7, 8, 9];
   begin
      pragma Assert (Capacity (X) >= 9);
   end Test_Sequences_With_Specific_Capacity;

   procedure Test_Bad_Sequences_With_Specific_Capacity with
     Global => null,
     Pre => not Short_Index;

   procedure Test_Bad_Sequences_With_Specific_Capacity is
      use Sequences_With_Specific_Capacity;
      X : T := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]; -- @PRECONDITION:FAIL
   begin
      null;
   end Test_Bad_Sequences_With_Specific_Capacity;

   procedure Test_Bad_Sequences_With_Specific_Capacity_2 with
     Global => null,
     Pre => Short_Index;

   procedure Test_Bad_Sequences_With_Specific_Capacity_2 is
      use Sequences_With_Specific_Capacity;
      X : T := [1, 2, 3, 4, 5, 6, 7, 8, 9]; -- @PRECONDITION:FAIL
   begin
      null;
   end Test_Bad_Sequences_With_Specific_Capacity_2;

   procedure Test_Sequences_With_Global_Capacity with
     Global => null,
     Pre => not Short_Index;

   procedure Test_Sequences_With_Global_Capacity is
      use Sequences_With_Global_Capacity;
      X : T := [1, 2, 3, 4, 5, 6, 7, 8, 9];
   begin
      null;
   end Test_Sequences_With_Global_Capacity;

   procedure Test_Bad_Sequences_With_Global_Capacity with
     Global => null,
     Pre => not Short_Index;

   procedure Test_Bad_Sequences_With_Global_Capacity is
      use Sequences_With_Global_Capacity;
      X : T := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]; -- @PRECONDITION:FAIL
   begin
      null;
   end Test_Bad_Sequences_With_Global_Capacity;

   procedure Test_Bad_Sequences_With_Global_Capacity_2 with
     Global => null,
     Pre => Short_Index;

   procedure Test_Bad_Sequences_With_Global_Capacity_2 is
      use Sequences_With_Global_Capacity;
      X : T := [1, 2, 3, 4, 5, 6, 7, 8, 9]; -- @PRECONDITION:FAIL
   begin
      null;
   end Test_Bad_Sequences_With_Global_Capacity_2;


begin
   null;
end;
