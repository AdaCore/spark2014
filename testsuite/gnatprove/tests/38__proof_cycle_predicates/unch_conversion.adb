with Ada.Unchecked_Conversion;

procedure Unch_Conversion with SPARK_Mode is
   type T is record A : Integer; end record;

   function F (V : T) return Boolean with Pre => True, Post =>  False;

   subtype R is T with Predicate => F (R);

   function Conv is new Ada.Unchecked_Conversion (T, R);

   function F (V : T) return Boolean
   is (Conv (V).A = 1);

begin
   null;
end;
