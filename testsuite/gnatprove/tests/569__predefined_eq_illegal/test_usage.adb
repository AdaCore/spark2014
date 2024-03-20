procedure Test_Usage with SPARK_Mode is

   --  Accepted annotations

   package OK_No_Eq is
      type T is private with
        Annotate => (GNATprove, Predefined_Equality, "No_Equality");
   private
      pragma SPARK_Mode (Off);
      type T is access Integer;
   end OK_No_Eq;

   package OK_Only_Null is
      type T is private with
        Annotate => (GNATprove, Predefined_Equality, "Only_Null");
      C : constant T with
        Annotate => (GNATprove, Predefined_Equality, "Null_Value");
   private
      pragma SPARK_Mode (Off);
      type T is access Integer;
      C : constant T := null;
   end OK_Only_Null;

   --  Uses of equality

   procedure Use_No_Eq (X, Y : OK_No_Eq.T) is
      use OK_No_Eq;
      function F (X : T) return Boolean with
        Global => null,
        Import;
      subtype S is T with Predicate => F (S);
      OK : Boolean := X in S;
      KO1 : Boolean := X = Y;
      KO2 : Boolean := X in Y | S;
   begin
      null;
   end Use_No_Eq;

   procedure Use_Only_Null (X, Y : OK_Only_Null.T) is
      use OK_Only_Null;
      OK1 : Boolean := X = C or C = Y;
      subtype Not_Null is T with Predicate => Not_Null /= C;
      OK2 : Boolean := X in C | Not_Null or C in Not_Null;
      KO1 : Boolean := X = Y;
      KO2 : Boolean := X in Y | Not_Null;
   begin
      null;
   end Use_Only_Null;

   --  Test that the annotation is properly handled on normal derivation

   package OK_Only_Null_Derived is
      type T is private;
      C : constant T;
   private
      type T is new OK_Only_Null.T;
      C : constant T := T (OK_Only_Null.C);
   end OK_Only_Null_Derived;

   procedure Use_Only_Null_Derived (X, Y : OK_Only_Null_Derived.T) is
      use OK_Only_Null_Derived;
      OK1 : Boolean := X = C or C = Y;
      subtype Not_Null is T with Predicate => Not_Null /= C;
      OK2 : Boolean := X in C | Not_Null or C in Not_Null;
      KO1 : Boolean := X = Y;
      KO2 : Boolean := X in Y | Not_Null;
   begin
      null;
   end Use_Only_Null_Derived;

   --  Test that the annotation is properly handled on tagged derivation.
   --  The predefined equality of T is used in Child.

   package OK_No_Eq_Tagged_1 is
      package Nested is
         type T is tagged private with
           Annotate => (GNATprove, Predefined_Equality, "No_Equality");
      private
         pragma SPARK_Mode (Off);
         type Int_Acc is access Integer;
         type T is tagged record
            F : Int_Acc;
         end record;
      end Nested;
      use Nested;

      type Child is new T with record
         F : Integer;
      end record;
   end OK_No_Eq_Tagged_1;

   procedure Use_No_Eq_Tagged_1 (X, Y : OK_No_Eq_Tagged_1.Child) is
      use OK_No_Eq_Tagged_1;
      function F (X : Child) return Boolean with
        Global => null,
        Import;
      subtype S is Child with Predicate => F (S);
      OK  : Boolean := X in S;
      KO1 : Boolean := X = Y;
      KO2 : Boolean := X in Y | S;
   begin
      null;
   end Use_No_Eq_Tagged_1;

   --  The predefined equality of T is not used in Child

   package OK_No_Eq_Tagged_2 is
      package Nested is
         type T is tagged private with
           Annotate => (GNATprove, Predefined_Equality, "No_Equality");
         function "=" (X, Y : T) return Boolean;
      private
         pragma SPARK_Mode (Off);
         type Int_Acc is access Integer;
         type T is tagged record
            F : Int_Acc;
         end record;
         function "=" (X, Y : T) return Boolean is
           ((X.F = null) = (Y.F = null)
            and then (if X.F /= null then X.F.all = Y.F.all));
      end Nested;
      use Nested;

      type Child is new T with record
         F : Integer;
      end record;
   end OK_No_Eq_Tagged_2;

   procedure Use_No_Eq_Tagged_2 (X, Y : OK_No_Eq_Tagged_2.Child) is
      use OK_No_Eq_Tagged_2;
      OK : Boolean := X = Y;
   begin
      null;
   end Use_No_Eq_Tagged_2;

begin
   null;
end Test_Usage;
