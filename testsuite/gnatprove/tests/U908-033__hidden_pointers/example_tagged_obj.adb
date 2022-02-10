with Interfaces; use Interfaces;
with Ada.Numerics.Big_Numbers.Big_Integers; use Ada.Numerics.Big_Numbers.Big_Integers;
with Pointers_With_Aliasing;

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

   package Pointers_To_Obj is new Pointers_With_Aliasing (Object'Class);

   use Pointers_To_Obj;
   use Memory_Model;

   package P2 is
      type Child is new Object with record
         F : Natural;
         G : Natural;
      end record;

      --  Lemma: Equality on Child is still an equivalence
      function Witness (O : Child) return Big_Integer is
        (To_Big_Integer (O.F) * 2_147_483_648 + To_Big_Integer (O.G));
      function "=" (O1, O2 : Child) return Boolean is
        (O1.F = O2.F and O1.G = O2.G);
   end P2;
   use P2;

   X1 : Pointer;
   X2 : Pointer;
   X3 : Pointer;
   X1_B : Pointer;

   procedure Swap (X, Y : in out Pointer) with
     Post => X = Y'Old and Y = X'Old
   is
      Tmp : constant Pointer := X;
   begin
      X := Y;
      Y := Tmp;
   end Swap;

   procedure Swap_Val (X, Y : Pointer) with
     Pre  => Valid (Memory, Address (X)) and then Valid (Memory, Address (Y)),
     Post => Deref (X) = Deref (Y)'Old and Deref (Y) = Deref (X)'Old
        and (for all Q of Memory'Old => Valid (Memory, Q))
        and (for all Q of Memory => Valid (Memory'Old, Q))
        and (for all Q of Memory =>
               (if Q not in Address (X) | Address (Y) then Get (Memory, Q) = Get (Memory'Old, Q)))
   is
      Tmp : constant Object'Class := Deref (X);
   begin
      Assign (X, Deref (Y));
      Assign (Y, Tmp);
   end Swap_Val;

   function Ignore (X : Object'Class) return Boolean with Import;

   procedure Update_In_Place (X : Pointer; New_F : Positive) with
     Pre => Valid (Memory, Address (X)) and then Deref (X) in Child,
     Post =>
        --  Deref (X) = Object'Class ((Child (Deref (X)'Old) with delta F => New_F))
        Deref (X) in Child and Child (Deref (X)) = (New_F, Child (Deref (X)).G'Old)
        and (for all Q of Memory'Old => Valid (Memory, Q))
        and (for all Q of Memory => Valid (Memory'Old, Q))
        and (for all Q of Memory =>
               (if Q /= Address (X) then Get (Memory, Q) = Get (Memory'Old, Q)))
   is
      Mem_Access : access Memory_Type := Memory'Access;
      X_Content  : access Object'Class := Reference (Mem_Access, X);
   begin
      Child (X_Content.all).F := New_F;
   end Update_In_Place;

begin
   Create (Child'(F => 1, G => 4), X1);
   Create (Child'(F => 2, G => 5), X2);
   Create (Child'(F => 3, G => 6), X3);
   X1_B := X1; --  X1_B is an alias of X1
   pragma Assert (Child (Deref (X1_B)).F = 1);
   Swap (X1, X2);
   Swap_Val (X1, X2);
   pragma Assert (Child (Deref (X1)).F = 1);
   pragma Assert (Child (Deref (X2)).F = 2);
   pragma Assert (Child (Deref (X3)).F = 3);
   pragma Assert (Child (Deref (X1_B)).F = 2); --  X1_B is now an alias of X2
   Update_In_Place (X2, 8);
   pragma Assert (Child (Deref (X2)).F = 8);
   pragma Assert (Child (Deref (X1_B)).F = 8);
end Example_Tagged_Obj;
