with Interfaces; use Interfaces;
with SPARK.Pointers.Pointers_With_Aliasing;

procedure Example_Untagged_Obj with SPARK_Mode is
   type Object is record
      F : Integer;
      G : Integer;
   end record;

   package Pointers_To_Obj is new SPARK.Pointers.Pointers_With_Aliasing (Object);

   use Pointers_To_Obj;
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
     Pre => Valid (Memory, Address (X)) and Valid (Memory, Address (Y)),
     Post => Deref (X) = Deref (Y)'Old and Deref (Y) = Deref (X)'Old
     and Allocates (Memory'Old, Memory, None)
     and Deallocates (Memory'Old, Memory, None)
     and Writes (Memory'Old, Memory, [for A in Address_Type => A in Address (X) | Address (Y)])
   is
      Tmp : constant Object := Deref (X);
   begin
      Assign (X, Deref (Y));
      Assign (Y, Tmp);
   end Swap_Val;

   procedure Update_In_Place (X : Pointer; New_F : Positive) with
     Pre => Valid (Memory, Address (X)),
     Post => Deref (X) = (Deref (X)'Old with delta F => New_F)
     and Allocates (Memory'Old, Memory, None)
     and Deallocates (Memory'Old, Memory, None)
     and Writes (Memory'Old, Memory, Only (Address (X)))
   is
      Mem_Access : access Memory_Type := Memory'Access;
      X_Content  : access Object := Reference (Mem_Access, X);
   begin
      X_Content.F := New_F;
   end Update_In_Place;
begin
   Create (Object'(F => 1, G => 4), X1);
   Create (Object'(F => 2, G => 5), X2);
   Create (Object'(F => 3, G => 6), X3);
   X1_B := X1; --  X1_B is an alias of X1
   pragma Assert (Deref (X1_B).F = 1);
   Swap (X1, X2);
   Swap_Val (X1, X2);
   pragma Assert (Deref (X1).F = 1);
   pragma Assert (Deref (X2).F = 2);
   pragma Assert (Deref (X3).F = 3);
   pragma Assert (Deref (X1_B).F = 2); --  X1_B is now an alias of X2
   Update_In_Place (X2, 8);
   pragma Assert (Deref (X2).F = 8);
   pragma Assert (Deref (X1_B).F = 8);
end Example_Untagged_Obj;
