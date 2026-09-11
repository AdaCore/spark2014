pragma Extensions_Allowed (On);

with Ada.Unchecked_Deallocation;
with SPARK.Pointers.Auto_Reclaimed.Global_Memory;

--  Auto_Reclaimed pointers to mutable data, on a plain designated object and
--  on one subject to ownership. Pointers are freely copyable, the designated
--  data can be modified through any of the copies, and nothing has to be
--  reclaimed by the user.

procedure Test_Auto_Reclaimed_Mutable with SPARK_Mode is
   pragma Unevaluated_Use_Of_Old (Allow);

   ---------------------------
   --  A plain designated object
   ---------------------------

   type Plain_Object is record
      F : Integer;
      G : Integer;
   end record;

   package Plain_Pointers is new
     SPARK.Pointers.Auto_Reclaimed.Global_Memory (Plain_Object);
   use Plain_Pointers;
   use Plain_Pointers.Memory_Model;

   function Id (O : Plain_Object) return Plain_Object is (O);
   package Plain_Ops is new Plain_Pointers.Copy_Operations (Id);
   use Plain_Ops;

   ------------------------------------------------
   --  A designated object subject to ownership  --
   ------------------------------------------------

   type Int_Acc is access Integer;

   type Owning_Object is record
      D : Int_Acc;
   end record;

   procedure Free is new Ada.Unchecked_Deallocation (Integer, Int_Acc);

   procedure Reclaim (X : in out Owning_Object)
   with Global => null, Always_Terminates, Post => X.D = null
   is
   begin
      Free (X.D);
   end Reclaim;

   package Owning_Pointers is new
     SPARK.Pointers.Auto_Reclaimed.Global_Memory (Owning_Object, Reclaim);

   function Make (V : Integer) return Owning_Object
   is (D => new Integer'(V));

   procedure Create_Owning is new Owning_Pointers.Create (Integer, Make);

   --  The designated object owns a cell, so a copy of it has to duplicate
   --  that cell.

   function Copy_Owning (O : Owning_Object) return Owning_Object
   with Global => null
   is
   begin
      if O.D = null then
         return (D => null);
      else
         return (D => new Integer'(O.D.all));
      end if;
   end Copy_Owning;

   package Owning_Ops is new Owning_Pointers.Copy_Operations (Copy_Owning);

begin
   Distinct_Cells :
   declare
      P, Q : Pointer;
   begin
      Plain_Ops.Create_Copy ((F => 1, G => 2), P);
      Plain_Ops.Create_Copy ((F => 3, G => 4), Q);

      --  Two separately created cells are distinct: what is known about the
      --  first survives the creation of the second.

      pragma Assert (Static => P /= Q);
      pragma Assert (Deref (P).F = 1);
      pragma Assert (Deref (Q).F = 3);

      --  and survives a write through the second

      Assign (Q, (F => 30, G => 40));
      pragma Assert (Deref (P).F = 1);
      pragma Assert (Deref (Q).F = 30);
   end Distinct_Cells;

   Aliasing :
   declare
      P : Pointer;
   begin
      Plain_Ops.Create_Copy ((F => 1, G => 2), P);
      declare
         Q : constant Pointer := P;
         --  Q is an alias of P: writing through one is visible through the
         --  other. This is the point of the unit, and it is why the memory
         --  is modelled rather than hidden.
      begin
         pragma Assert (Static => P = Q);
         Assign (Q, (F => 7, G => 8));
         pragma Assert (Deref (P).F = 7);
         pragma Assert (Deref (P).G = 8);
      end;
   end Aliasing;

   Owning :
   declare
      use Owning_Pointers.Memory_Model;
      P : Owning_Pointers.Pointer;
   begin
      Create_Owning (42, P);
      pragma Assert
        (Static =>
           In_Memory (Owning_Pointers.Memory_Model.Model, P));

      --  Assign reclaims the designated value before overwriting it, so the
      --  cell allocated above is not leaked, and the library reclaims the
      --  last one when P disappears. Neither is visible in the model, which
      --  is why Assign has no reclamation precondition and why there is no
      --  leak check on P at the end of this block. Assign copies its
      --  argument rather than taking it, so New_Value is still owned here.

      declare
         New_Value : Owning_Object := (D => new Integer'(43));
      begin
         Owning_Ops.Assign (P, New_Value);
         Reclaim (New_Value);
      end;
      pragma Assert
        (Static =>
           In_Memory (Owning_Pointers.Memory_Model.Model, P));
   end Owning;
end Test_Auto_Reclaimed_Mutable;
