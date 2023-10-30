procedure Test with SPARK_Mode is
   pragma Unevaluated_Use_Of_Old (Allow);

   package Seqs is
      type Index_Type is new Integer range 1 .. 10;
      subtype Ext_Index is Index_Type'Base range 0 .. 10;

      type Element_Type is new Integer;

      type T is private with
        Aggregate => (Empty       => Empty,
                      Add_Unnamed => Append),
        Annotate => (GNATprove, Container_Aggregates, "Predefined_Sequences");

      function Empty return T with
        Post => Last (Empty'Result) = 0;

      procedure Append (X : in out T; E : Element_Type) with
	Always_Terminates,
        Pre => Last (X) < 10,
        Post => Last (X) = Last (X)'Old + 1
        and then Get (X, Last (X)) = E
        and then (for all I in 1 .. Last (X) - 1 =>
                    Get (X, I) =  Get (X'Old, I));

      function Get (X : T; I : Index_Type) return Element_Type with
        Annotate => (GNATprove, Container_Aggregates, "Get"),
        Pre => I <= Last (X);

      function Last (X : T) return Ext_Index with
        Annotate => (GNATprove, Container_Aggregates, "Last");

      function First return Index_Type is (1) with
        Annotate => (GNATprove, Container_Aggregates, "First");

   private
      type T_Content is array (Index_Type) of Element_Type with
        Relaxed_Initialization;
      type T is record
         Content : T_Content;
         Top     : Ext_Index;
      end record with
        Ghost_Predicate =>
          (for all I in 1 .. Top => Content (I)'Initialized);

      function Get (X : T; I : Index_Type) return Element_Type is
        (X.Content (I));

      function Last (X : T) return Ext_Index is (X.Top);
   end Seqs;

   package body Seqs is

      function Empty return T is
      begin
         return Res : T do
            Res.Top := 0;
         end return;
      end Empty;

      procedure Append (X : in out T; E : Element_Type) is
      begin
         X.Content (X.Top + 1) := E;
         X.Top := X.Top + 1;
      end Append;

   end Seqs;

   package Sets is
      type Element_Type is range 1 .. 100;
      type T is private with
        Aggregate => (Empty       => Empty,
                      Add_Unnamed => Insert),
        Annotate => (GNATprove, Container_Aggregates, "Predefined_Sets");

      function Empty return T;
      procedure Insert (X : in out T; E : Element_Type) with
	Always_Terminates,
        Post => Length (X) <= Length (X)'Old + 1
        and then Contains (X, E)
        and then (for all F in Element_Type =>
                    (if F /= E then Contains (X, F) = Contains (X'Old, F)));

      function Contains (X : T; E : Element_Type) return Boolean with
        Annotate => (GNATprove, Container_Aggregates, "Contains");

      type Length_Type is range 0 .. 100;

      function Length (X : T) return Length_Type with
        Post => Length'Result = Length_Rec (X),
        Annotate => (GNATprove, Container_Aggregates, "Length");

      function Length_Rec (X : T) return Length_Type with
        Ghost;

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

      function Length_Rec (X : T; I : Length_Type) return Length_Type with
        Ghost,
        Subprogram_Variant => (Decreases => I),
        Post => Length_Rec'Result <= I;

      procedure Lemma_Length_Empty (X : T; I : Length_Type) with
        Ghost,
        Annotate => (GNATprove, Automatic_Instantiation),
        Pre => (for all K in 1 .. I => not X.Content (Element_Type (K))),
        Post => Length_Rec (X, I) = 0,
        Subprogram_Variant => (Decreases => I);

      function Length_Rec (X : T; I : Length_Type) return Length_Type is
        (if I = 0 then 0
         else Length_Rec (X, I - 1) +
         (if X.Content (Element_Type (I)) then 1 else 0));

      function Length_Rec (X : T) return Length_Type is
        (Length_Rec (X, 100));
   end Sets;

   package body Sets is

      procedure Lemma_Length_Empty (X : T; I : Length_Type) is
      begin
         if I /= 0 then
            Lemma_Length_Empty (X, I - 1);
         end if;
      end Lemma_Length_Empty;

      procedure Insert (X : in out T; E : Element_Type) is
         X_Old : constant T := X with Ghost;
         procedure Prove_Length with Ghost;
         procedure Prove_Length is
         begin
            for I in X.Content'Range loop
               pragma Loop_Invariant
                 (if I < E
                  then Length_Rec (X, Length_Type (I)) =
                    Length_Rec (X_Old, Length_Type (I)));
               pragma Loop_Invariant
                 (if I >= E
                  then Length_Rec (X, Length_Type (I))
                  <= Length_Rec (X_Old, Length_Type (I)) + 1);
            end loop;
         end Prove_Length;
      begin
         X.Content (E) := True;
         Prove_Length;
      end Insert;

      function Length (X : T) return Length_Type is
      begin
         return Res : Length_Type := 0 do
            for I in X.Content'Range loop
               if X.Content (I) then
                  Res := Res + 1;
               end if;
               pragma Loop_Invariant
                 (Res = Length_Rec (X, Length_Type (I)));
            end loop;
         end return;
      end Length;
   end Sets;

   package Partial_Maps is
      Max : constant Natural := 20;
      type Key_Type is range 1 .. 100;
      type Element_Type is new Integer;
      type T is private with
        Aggregate => (Empty       => Empty,
                      Add_Named => Insert),
        Annotate => (GNATprove, Container_Aggregates, "Predefined_Maps");

      function T_Eq (X, Y : T) return Boolean with
        Ghost,
        Import,
        Global => null,
        Annotate => (GNATprove, Logical_Equal);

      function Copy (X : T) return T with
        Ghost,
        Import,
        Global => null,
        Post => T_Eq (X, Copy'Result);

      function Empty return T;
      procedure Insert (X : in out T; K : Key_Type; E : Element_Type) with
	Always_Terminates,
        Pre  => not Has_Key (X, K),
        Post => Length (X) = Length (X)'Old + 1
        and then Has_Key (X, K)
        and then Get (X, K) = E
        and then (for all L in Key_Type =>
                    (if L /= K then Has_Key (X, L) = Has_Key (Copy (X)'Old, L)))
        and then (for all L in Key_Type =>
                    (if L /= K and Has_Key (X, L) then
                         Get (X, L) = Get (Copy (X)'Old, L)));

      function Has_Key (X : T; K : Key_Type) return Boolean with
        Annotate => (GNATprove, Container_Aggregates, "Has_Key"),
        Subprogram_Variant => (Structural => X);

      function Get (X : T; K : Key_Type) return Element_Type with
        Pre => Has_Key (X, K),
        Annotate => (GNATprove, Container_Aggregates, "Get"),
        Subprogram_Variant => (Structural => X);

      function Eq_Key (X, Y : Key_Type) return Boolean is (X = Y) with
        Annotate => (GNATprove, Container_Aggregates, "Equivalent_Keys");

      type Length_Type is range 0 .. 100;

      function Length (X : T) return Length_Type with
        Annotate => (GNATprove, Container_Aggregates, "Length"),
        Subprogram_Variant => (Structural => X);

   private
      type Pair is record
         K : Key_Type;
         E : Element_Type;
      end record;
      type T_Cell;
      type T is access T_Cell;
      type T_Cell is record
         P : Pair;
         N : T;
      end record;

      function Empty return T is
        (null);

      function Has_Key (X : T; K : Key_Type) return Boolean is
        (if X = null then False else K = X.P.K or else Has_Key (X.N, K));

      function Get (X : T; K : Key_Type) return Element_Type is
        (if K = X.P.K then X.P.E else Get (X.N, K));

      function Length (X : T) return Length_Type is
        (if X = null then 0 else Length (X.N) + 1);
   end Partial_Maps;

   package body Partial_Maps is
      procedure Insert (X : in out T; K : Key_Type; E : Element_Type) is
      begin
         X := new T_Cell'((K, E), X);
      end Insert;
   end Partial_Maps;

   package Total_Maps is
      Max : constant Natural := 20;
      type Key_Type is range 1 .. 100;
      type Element_Type is new Integer;
      type T is private with
        Aggregate => (Empty       => Empty,
                      Add_Named => Insert),
        Annotate => (GNATprove, Container_Aggregates, "Predefined_Maps");

      function T_Eq (X, Y : T) return Boolean with
        Ghost,
        Import,
        Global => null,
        Annotate => (GNATprove, Logical_Equal);

      function Copy (X : T) return T with
        Ghost,
        Import,
        Global => null,
        Post => T_Eq (X, Copy'Result);

      function Empty return T;
      procedure Insert (X : in out T; K : Key_Type; E : Element_Type) with
	Always_Terminates,
        Post => Get (X, K) = E
        and then (for all L in Key_Type =>
                    (if L /= K then
                         Get (X, L) = Get (Copy (X)'Old, L)));

      function Default_Value return Element_Type is (0) with
        Annotate => (GNATprove, Container_Aggregates, "Default_Item");

      function Get (X : T; K : Key_Type) return Element_Type with
        Annotate => (GNATprove, Container_Aggregates, "Get"),
        Subprogram_Variant => (Structural => X);

      function Eq_Key (X, Y : Key_Type) return Boolean is (X = Y) with
        Annotate => (GNATprove, Container_Aggregates, "Equivalent_Keys");

   private
      type Pair is record
         K : Key_Type;
         E : Element_Type;
      end record;
      type T_Cell;
      type T is access T_Cell;
      type T_Cell is record
         P : Pair;
         N : T;
      end record;

      function Empty return T is
        (null);

      function Get (X : T; K : Key_Type) return Element_Type is
        (if X = null then 0 elsif K = X.P.K then X.P.E else Get (X.N, K));
   end Total_Maps;

   package body Total_Maps is
      procedure Insert (X : in out T; K : Key_Type; E : Element_Type) is
      begin
         X := new T_Cell'((K, E), X);
      end Insert;
   end Total_Maps;

   procedure Test_Sets (E : Sets.Element_Type) with
     Global => null;

   procedure Test_Sets (E : Sets.Element_Type) is
      use Sets;
      X : T := [1, 2, 3, 4, 5];
      Y : T := [];
   begin
      pragma Assert (Length (X) <= 5);
      pragma Assert (Contains (X, E) = (E in 1 | 2 | 3 | 4 | 5));
      pragma Assert (Length (Y) = 0);
      pragma Assert (not Contains (Y, E));
      pragma Assert (False); --  @ASSERT:FAIL
   end Test_Sets;

   procedure Test_Partial_Maps (K : Partial_Maps.Key_Type) with
     Global => null;

   procedure Test_Partial_Maps (K : Partial_Maps.Key_Type)  is
      use Partial_Maps;
      X : T := [1 => 1, 2 => 2, 3 => 3, 4 => 4, 5 => 5];
      Y : T := [];
   begin
      pragma Assert (Length (X) = 5);
      pragma Assert (Has_Key (X, K) = (K in 1 | 2 | 3 | 4 | 5));
      for I in Key_Type range 1 .. 5 loop
         pragma Assert (Get (X, I) = Element_Type (I));
      end loop;
      pragma Assert (Length (Y) = 0);
      pragma Assert (not Has_Key (Y, K));
      pragma Assert (False); --  @ASSERT:FAIL
   end Test_Partial_Maps;

   procedure Test_Bad_Partial_Maps with
     Global => null;

   procedure Test_Bad_Partial_Maps  is
      use Partial_Maps;
      X : T := [1 => 1, 2 => 2, 3 => 3, 4 => 4, 5 => 5, 2 => 2]; -- @PRECONDITION:FAIL
   begin
      null;
   end Test_Bad_Partial_Maps;

   procedure Test_Total_Maps (K : Total_Maps.Key_Type) with
     Global => null;

   procedure Test_Total_Maps (K : Total_Maps.Key_Type)  is
      use Total_Maps;
      X : T := [1 => 1, 2 => 2, 3 => 3, 4 => 4, 5 => 5];
      Y : T := [];
   begin
      for I in Key_Type range 1 .. 5 loop
         pragma Assert (Get (X, I) = Element_Type (I));
      end loop;
      pragma Assert (if K not in 1 | 2 | 3 | 4 | 5 then Get (X, K) = 0);
      pragma Assert (Get (Y, K) = 0);
      pragma Assert (False); --  @ASSERT:FAIL
   end Test_Total_Maps;

   procedure Test_Bad_Total_Maps with
     Global => null;

   procedure Test_Bad_Total_Maps  is
      use Partial_Maps;
      X : T := [1 => 1, 2 => 2, 3 => 3, 1 => 4, 5 => 5]; -- @PRECONDITION:FAIL
   begin
      null;
   end Test_Bad_Total_Maps;

   procedure Test_Seqs with
     Global => null;

   procedure Test_Seqs is
      use Seqs;
      X : T := [1, 2, 3, 4, 5];
      Y : T := [];
   begin
      pragma Assert (Last (X) = 5);
      for I in Index_Type range 1 .. 5 loop
         pragma Assert (Get (X, I) = Element_Type (I));
      end loop;
      pragma Assert (Last (Y) = 0);
      pragma Assert (False); --  @ASSERT:FAIL
   end Test_Seqs;

   procedure Test_Bad_Seqs with
     Global => null;

   procedure Test_Bad_Seqs is
      use Seqs;
      X : T := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]; -- @PRECONDITION:FAIL
   begin
      null;
   end Test_Bad_Seqs;

begin
   null;
end Test;
