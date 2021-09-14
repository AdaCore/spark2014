with Interfaces; use Interfaces;
with Ada.Numerics.Big_Numbers.Big_Integers; use Ada.Numerics.Big_Numbers.Big_Integers;
with Hidden_Pointers;

procedure Example_Tagged_Obj with SPARK_Mode is
   package P1 is
      type Object is tagged null record;

      --  Lemma: Equality on Object is an equivalence.
      --  It will need to be proved for each new derivation
      function Witness (O : Object) return Big_Integer is (0);
      function "=" (O1, O2 : Object) return Boolean is
        (True)
      with Post'Class => "="'Result = (Witness (O1) = Witness (O2));
   end P1;
   use P1;

   package Pointers_To_Obj is new Hidden_Pointers (Object'Class);

   use Pointers_To_Obj;
   use Model;

   package P2 is
      type Child is new Object with record
         F : Integer;
      end record;

      --  Lemma: Equality on Child is still an equivalence
      function Witness (O : Child) return Big_Integer is (To_Big_Integer (O.F));
      function "=" (O1, O2 : Child) return Boolean is
        (O1.F = O2.F);
   end P2;
   use P2;

   X1 : Pointer;
   X2 : Pointer;
   X3 : Pointer;

   procedure Swap (X, Y : in out Pointer) with
     Post => X = Y'Old and Y = X'Old
   is
      Tmp : constant Pointer := X;
   begin
      X := Y;
      Y := Tmp;
   end Swap;

   procedure Swap_Val (X, Y : Pointer) with
     Pre  => Valid (My_Memory, Address (X)) and then Valid (My_Memory, Address (Y)),
     Post => Deref (X) = Deref (Y)'Old and Deref (Y) = Deref (X)'Old
        and (for all Q of My_Memory'Old => Valid (My_Memory, Q))
        and (for all Q of My_Memory => Valid (My_Memory'Old, Q))
        and (for all Q of My_Memory =>
               (if Q not in Address (X) | Address (Y) then Get (My_Memory, Q) = Get (My_Memory'Old, Q)))
   is
      Tmp : constant Object'Class := Deref (X);
   begin
      Assign (X, Deref (Y));
      Assign (Y, Tmp);
   end Swap_Val;
begin
   Create (Child'(F => 1), X1);
   Create (Child'(F => 2), X2);
   Create (Child'(F => 3), X3);
   Swap (X1, X2);
   Swap_Val (X1, X2);
   pragma Assert (Child (Deref (X1)).F = 1);
   pragma Assert (Child (Deref (X2)).F = 2);
   pragma Assert (Child (Deref (X3)).F = 3);
end Example_Tagged_Obj;
