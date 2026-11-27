procedure Flow_Predicates (Selected : Integer) with
  SPARK_Mode,
  Pre => Selected in 1 .. 4
is
   type Vector is array (1 .. 4) of Integer;
   X : constant Vector := [others => 0];

   function Matches (I : Integer) return Boolean is
     (I in 1 | 4 or else I = Selected);
   subtype Direct is Integer range 1 .. 4
     with Dynamic_Predicate => Direct in 1 | 4 or else Direct = Selected;
   subtype Indirect is Integer range 1 .. 4
     with Dynamic_Predicate => Matches (Indirect);

   procedure Delta_Good (Result : out Vector) with
     Global => (Input => Selected),
     Depends => (Result => Selected)
   is
   begin
      Result := (X with delta Direct => 9);
   end Delta_Good;

   procedure Update_Good (Result : out Vector) with
     Global => (Input => Selected),
     Depends => (Result => Selected)
   is
   begin
      Result := X'Update (Indirect range 1 .. 4 => 9);
   end Update_Good;

   procedure Delta_Bad (Result : out Vector) with
     Global => (Input => Selected),
     Depends => (Result => null, null => Selected)
   is
   begin
      Result := (X with delta Indirect => 9);
   end Delta_Bad;

   procedure Update_Bad (Result : out Vector) with
     Global => (Input => Selected),
     Depends => (Result => null, null => Selected)
   is
   begin
      Result := X'Update (Direct range 1 .. 4 => 9);
   end Update_Bad;

   A, B, C, D : Vector;
begin
   Delta_Good (A);
   Update_Good (B);
   Delta_Bad (C);
   Update_Bad (D);
end Flow_Predicates;
