with Rec_Ids; use Rec_Ids;

package P with SPARK_Mode is

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
        (Y in C (P_Rec_Id (X.F)) .. C (X.L));
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
           Has_Element => Has_Element,
           Element     => Element);
      type C is private;

      function First (X : T) return C;
      function Next (X : T; Y : C) return C with
        Pre => Has_Element (X, Y);
      function Has_Element (X : T; Y : C) return Boolean;
      function Model (X : T) return P1.T with
        Annotate => (GNATprove, Iterable_For_Proof, "Model");
      function Element (X : T; Y : C) return Integer with
        Pre  => Has_Element (X, Y);
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
   end P2;
end P;
