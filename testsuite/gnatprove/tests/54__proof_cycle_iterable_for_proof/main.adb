--  This test contains 7 versions of the same container with an Iterable
--  aspect. The first one is correct, while the other 6 introduce some form
--  of recursion, either for proof, for execution, or for both.

procedure Main with SPARK_Mode, Always_Terminates
is
   type Int_Arr is array (Positive range <>) of Integer;

   package P1 is
      type T is private with
        Iterable =>
          (First       => First,
           Next        => Next,
           Has_Element => Has_Element,
           Element     => Element);
      type C is private;
      function First (X : T) return C;
      function Next (X : T; Y : C) return C with
        Pre => Has_Element (X, Y);
      function Has_Element (X : T; Y : C) return Boolean;
      function Element (X : T; Y : C) return Integer with
        Pre  => Has_Element (X, Y);
      function From_Array (X : Int_Arr) return T;
   private
      Max : constant := 100;
      subtype Small_Nat is Natural range 0 .. Max;
      subtype Small_Pos is Positive range 1 .. Max;
      type T (F : Small_Pos := 1; L : Small_Nat := 0) is record
         Content : Int_Arr (F .. L);
      end record;
      type C is new Integer;
      function First (X : T) return C is (C (X.F));
      function Next (X : T; Y : C) return C is (Y + 1);
      function Has_Element (X : T; Y : C) return Boolean is
        (Y in C (X.F) .. C (X.L));
      function Element (X : T; Y : C) return Integer is
        (X.Content (Integer (Y)));
      function From_Array (X : Int_Arr) return T is
        (if X'Length = 0 or else X'Last > Max
         then (F => 1, L => 0, Content => (1 .. 0 => 0))
         else (F => X'First, L => X'Last, Content => X));
   end P1;

   package P2 is
      type T is private with
        Iterable =>
          (First       => First,
           Next        => Next,
           Has_Element => Has_Element);
      type C is private;

      function Is_Empty (X : T) return Boolean;
      function First (X : T) return C with
        Post => (if not Is_Empty (X)
                 then (for some Y in X => Y = First'Result));
      --  Recursive call

      function Next (X : T; Y : C) return C with
        Pre => Has_Element (X, Y);
      function Has_Element (X : T; Y : C) return Boolean;
   private
      Max : constant := 100;
      subtype Small_Nat is Natural range 0 .. Max;
      subtype Small_Pos is Positive range 1 .. Max;
      type T (F : Small_Pos := 1; L : Small_Nat := 0) is record
         Content : Int_Arr (F .. L);
      end record;
      type C is new Integer;
      function Is_Empty (X : T) return Boolean is (X.L < X.F);
      function First (X : T) return C is (C (X.F));
      function Next (X : T; Y : C) return C is (Y + 1);
      function Has_Element (X : T; Y : C) return Boolean is
        (Y in C (X.F) .. C (X.L));
   end P2;

   package P3 is
      type T is private with
        Iterable =>
          (First       => First,
           Next        => Next,
           Has_Element => Has_Element);
      type C is private;

      function First (X : T) return C;
      function Last (X : T) return C;
      function Next (X : T; Y : C) return C with
        Pre  => Has_Element (X, Y),
        Post => (if Y /= Last (X)
                 then (for some Y in X => Y = Next'Result));
      --  Recursive call

      function Has_Element (X : T; Y : C) return Boolean;
   private
      Max : constant := 100;
      subtype Small_Nat is Natural range 0 .. Max;
      subtype Small_Pos is Positive range 1 .. Max;
      type T (F : Small_Pos := 1; L : Small_Nat := 0) is record
         Content : Int_Arr (F .. L);
      end record;
      type C is new Integer;
      function Last (X : T) return C is (C (X.L));
      function First (X : T) return C is (C (X.F));
      function Next (X : T; Y : C) return C is (Y + 1);
      function Has_Element (X : T; Y : C) return Boolean is
        (Y in C (X.F) .. C (X.L));
   end P3;

   package P4 is
      type T is private with
        Iterable =>
          (First       => First,
           Next        => Next,
           Has_Element => Has_Element);
      type C is private;

      function First (X : T) return C;
      function Next (X : T; Y : C) return C with
        Pre => Has_Element (X, Y);
      function Has_Element (X : T; Y : C) return Boolean with
        Post => Has_Element'Result = (for some Z in X => Y = Z);
      --  Recursive call

   private
      Max : constant := 100;
      subtype Small_Nat is Natural range 0 .. Max;
      subtype Small_Pos is Positive range 1 .. Max;
      type T (F : Small_Pos := 1; L : Small_Nat := 0) is record
         Content : Int_Arr (F .. L);
      end record;
      type C is new Integer;
      function First (X : T) return C is (C (X.F));
      function Next (X : T; Y : C) return C is (Y + 1);
      function Has_Element (X : T; Y : C) return Boolean is
        (Y in C (X.F) .. C (X.L));
   end P4;

   package P5 is
      type T is private with
        Iterable =>
          (First       => First,
           Next        => Next,
           Has_Element => Has_Element,
           Element     => Element);
      type C is private;

      function First (X : T) return C;
      function Next (X : T; Y : C) return C with
        Pre => Has_Element (X, Y);
      function Has_Element (X : T; Y : C) return Boolean;
      function Element (X : T; Y : C) return Integer with
        Pre  => Has_Element (X, Y),
        Post => (for some E of X => E = Element'Result);
      --  Recursive call

   private
      Max : constant := 100;
      subtype Small_Nat is Natural range 0 .. Max;
      subtype Small_Pos is Positive range 1 .. Max;
      type T (F : Small_Pos := 1; L : Small_Nat := 0) is record
         Content : Int_Arr (F .. L);
      end record;
      type C is new Integer;
      function First (X : T) return C is (C (X.F));
      function Next (X : T; Y : C) return C is (Y + 1);
      function Has_Element (X : T; Y : C) return Boolean is
        (Y in C (X.F) .. C (X.L));
      function Element (X : T; Y : C) return Integer is
        (X.Content (Integer (Y)));
   end P5;

   package P6 is
      type T is private with
        Iterable =>
          (First       => First,
           Next        => Next,
           Has_Element => Has_Element,
           Element     => Element);
      type C is private;

      function First (X : T) return C;
      function Next (X : T; Y : C) return C with
        Pre => Has_Element (X, Y);
      function Has_Element (X : T; Y : C) return Boolean;
      function Contains (X : T; E : Integer) return Boolean with
        Post => Contains'Result = (for some F of X => E = F);
      function Element (X : T; Y : C) return Integer with
        Pre  => Has_Element (X, Y);
      pragma Annotate (GNATprove, Iterable_For_Proof, "Contains", Contains);
      --  Recursive call - for proof only - because of the iterable_for_proof
      --  annotation.

   private
      Max : constant := 100;
      subtype Small_Nat is Natural range 0 .. Max;
      subtype Small_Pos is Positive range 1 .. Max;
      type T (F : Small_Pos := 1; L : Small_Nat := 0) is record
         Content : Int_Arr (F .. L);
      end record;
      type C is new Integer;
      function First (X : T) return C is (C (X.F));
      function Next (X : T; Y : C) return C is (Y + 1);
      function Has_Element (X : T; Y : C) return Boolean is
        (Y in C (X.F) .. C (X.L));
      function Element (X : T; Y : C) return Integer is
        (X.Content (Integer (Y)));
      function Contains (X : T; E : Integer) return Boolean is
        (for some F of X.Content => F = E);
   end P6;

   package P7 is
      type T is private with
        Iterable =>
          (First       => First,
           Next        => Next,
           Has_Element => Has_Element,
           Element     => Element);
      type C is private;

      function First (X : T) return C;
      function Next (X : T; Y : C) return C with
        Pre => Has_Element (X, Y);
      function Has_Element (X : T; Y : C) return Boolean;
      function Model (X : T) return P1.T with
        Post => (for all E of X => (for some F of Model'Result => E = F));
      function Element (X : T; Y : C) return Integer with
        Pre  => Has_Element (X, Y);
      pragma Annotate (GNATprove, Iterable_For_Proof, "Model", Model);
      --  Recursive call - for proof only - because of the iterable_for_proof
      --  annotation.

   private
      Max : constant := 100;
      subtype Small_Nat is Natural range 0 .. Max;
      subtype Small_Pos is Positive range 1 .. Max;
      type T (F : Small_Pos := 1; L : Small_Nat := 0) is record
         Content : Int_Arr (F .. L);
      end record;
      type C is new Integer;
      function First (X : T) return C is (C (X.F));
      function Next (X : T; Y : C) return C is (Y + 1);
      function Has_Element (X : T; Y : C) return Boolean is
        (Y in C (X.F) .. C (X.L));
      function Element (X : T; Y : C) return Integer is
        (X.Content (Integer (Y)));
      function Model (X : T) return P1.T is
        (P1.From_Array (X.Content));
   end P7;

begin
   null;
end Main;
