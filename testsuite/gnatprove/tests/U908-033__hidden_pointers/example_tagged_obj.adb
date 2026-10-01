with Interfaces; use Interfaces;
with Ada.Numerics.Big_Numbers.Big_Integers; use Ada.Numerics.Big_Numbers.Big_Integers;
with SPARK.Pointers.Explicit_Reclamation.Global_Memory;

with P1; use P1;
with P2; use P2;

procedure Example_Tagged_Obj with SPARK_Mode is

   function Is_Reclaimed (Unused : Object'Class) return Boolean is (True)
   with Ghost => Static;

   package Pointers_To_Obj is new
     SPARK.Pointers.Explicit_Reclamation.Global_Memory (Object'Class, Is_Reclaimed);

   package Pointers_To_Obj_Copy_Operations is new
     Pointers_To_Obj.Copy_Operations;

   use Pointers_To_Obj;
   use Pointers_To_Obj_Copy_Operations;
   use Memory_Model;

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
     Pre  => (Static => In_Memory (Model (Memory), X)
              and then In_Memory (Model (Memory), Y)),
     Post => (Static => Deref (X) = Deref (Y)'Old and Deref (Y) = Deref (X)'Old
     and Allocates (Model (Memory)'Old, Model (Memory), None)
     and Deallocates (Model (Memory)'Old, Model (Memory), None)
     and Writes (Model (Memory)'Old, Model (Memory), Add (Only (X), Y)))
   is
      Tmp : constant Object'Class := Deref (X);
   begin
      Assign (X, Deref (Y));
      Assign (Y, Tmp);
   end Swap_Val;

   function Ignore (X : Object'Class) return Boolean with Import;

   procedure Update_In_Place (X : Pointer; New_F : Positive) with
     Pre => (Static => In_Memory (Model (Memory), X)
             and then Deref (X) in Child),
     Post => (Static =>
        --  Deref (X) = Object'Class ((Child (Deref (X)'Old) with delta F => New_F))
        Deref (X) in Child and Child (Deref (X)) = (New_F, Child (Deref (X)).G'Old)
     and Allocates (Model (Memory)'Old, Model (Memory), None)
     and Deallocates (Model (Memory)'Old, Model (Memory), None)
     and Writes (Model (Memory)'Old, Model (Memory), Only (X)))
   is
      X_Content : access Object'Class := Reference (Memory, X);
   begin
      Child (X_Content.all).F := New_F;
   end Update_In_Place;

begin
   Pointers_To_Obj_Copy_Operations.Create_Copy (Child'(F => 1, G => 4), X1);
   Pointers_To_Obj_Copy_Operations.Create_Copy (Child'(F => 2, G => 5), X2);
   Pointers_To_Obj_Copy_Operations.Create_Copy (Child'(F => 3, G => 6), X3);
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
