procedure Repr_Bad with SPARK_Mode is
   function Rand (X : Integer) return Boolean with Import;

   package Nested is
      type C_Int_Acc is access constant Integer;
      type Int_Acc is access Integer;
      type Nat_Array is array (Positive range <>) of Natural;
      type Root (Last : Natural) is tagged record
         F : Nat_Array (1 .. Last);
         G : not null Int_Acc;
      end record;
      function "=" (X, Y : Root) return Boolean is
        (X.F = Y.F and X.G.all = Y.G.all);
      --  Avoid pointer equality

      type Child is new Root with record
         H : not null C_Int_Acc;
      end record;
      --  Here we have pointer equality...

      subtype S is Child (Last => 10);
      type GrandChild is new S with null record;
   end Nested;
   use Nested;

   function Test (X, Y : GrandChild) return Boolean is (X = Y);
   --  Test should be rejected because "=" uses pointer equality once the
   --  resolution of tagged predefined equality is fixed in the frontend.
begin
   null;
end Repr_Bad;
