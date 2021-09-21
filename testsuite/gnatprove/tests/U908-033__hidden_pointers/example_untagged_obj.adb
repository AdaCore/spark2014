with Interfaces; use Interfaces;
with Hidden_Pointers;

procedure Example_Untagged_Obj with SPARK_Mode is
   type Object is record
      F : Integer;
   end record;

   package Pointers_To_Obj is new Hidden_Pointers (Object);

   use Pointers_To_Obj;
   use Model;

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
     Pre => Valid (My_Memory, Address (X)) and Valid (My_Memory, Address (Y)),
     Post => Deref (X) = Deref (Y)'Old and Deref (Y) = Deref (X)'Old
        and (for all Q of My_Memory'Old => Valid (My_Memory, Q))
        and (for all Q of My_Memory => Valid (My_Memory'Old, Q))
        and (for all Q of My_Memory =>
               (if Q not in Address (X) | Address (Y) then Get (My_Memory, Q) = Get (My_Memory'Old, Q)))
   is
      Tmp : constant Object := Deref (X);
   begin
      Assign (X, Deref (Y));
      Assign (Y, Tmp);
   end Swap_Val;
begin
   Create (Object'(F => 1), X1);
   Create (Object'(F => 2), X2);
   Create (Object'(F => 3), X3);
   X1_B := X1; --  X1_B is an alias of X1
   pragma Assert (Deref (X1_B).F = 1);
   Swap (X1, X2);
   Swap_Val (X1, X2);
   pragma Assert (Deref (X1).F = 1);
   pragma Assert (Deref (X2).F = 2);
   pragma Assert (Deref (X3).F = 3);
   pragma Assert (Deref (X1_B).F = 2); --  X1_B is now an alias of X2
end Example_Untagged_Obj;
