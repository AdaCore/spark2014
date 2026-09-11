pragma Extensions_Allowed (On);

with Ada.Unchecked_Deallocation;
with SPARK.Pointers.Auto_Reclaimed.Immutable;

--  Auto_Reclaimed pointers, on a plain designated object and on one subject to
--  ownership. Pointers are freely copyable and nothing has to be reclaimed by
--  the user in either case.

procedure Test_Auto_Reclaimed with SPARK_Mode is

   --------------------------------------------------------------
   --  A plain designated object: the Reclaim formal is defaulted --
   --------------------------------------------------------------

   type Plain_Object is record
      F : Integer;
      G : Integer;
   end record;

   package Plain_Pointers is new SPARK.Pointers.Auto_Reclaimed.Immutable (Plain_Object);
   use Plain_Pointers;

   function Id (O : Plain_Object) return Plain_Object is (O);
   function Create_Plain is new Plain_Pointers.Create (Plain_Object, Id);

   --  A designated object subject to ownership. Declared here so that the
   --  two scenarios below can be written as blocks of the main subprogram
   --  rather than as subprograms with no effect.

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
     SPARK.Pointers.Auto_Reclaimed.Immutable (Owning_Object, Reclaim);

   function Make (V : Integer) return Owning_Object
   is (D => new Integer'(V));

   function Create_Owning is new Owning_Pointers.Create (Integer, Make);

begin
   Plain :
   declare
      P : Pointer := Create_Plain ((F => 1, G => 2));
      Q : Pointer := P;
      --  Copying a pointer is free: no ownership is transferred, so P stays
      --  readable.
   begin
      pragma Assert (P /= Null_Pointer);
      pragma Assert (Q /= Null_Pointer);
      pragma Assert (Constant_Reference (P).F = 1);
      pragma Assert (Constant_Reference (P).G = 2);

      --  The copy designates the same value

      pragma Assert (Static => Logical_Eq (P, Q));
      pragma Assert (Static => Extensional_Eq (P, Q));
      pragma Assert (Constant_Reference (Q).F = 1);

      --  A pointer is modelled by the value it designates, so two pointers
      --  created from equal values are logically equal.

      declare
         R : constant Pointer := Create_Plain ((F => 1, G => 2));
      begin
         pragma Assert (Static => Logical_Eq (P, R));
      end;
   end Plain;

   Owning :
   declare
      use Owning_Pointers;
      P : Owning_Pointers.Pointer := Create_Owning (42);
      Q : Owning_Pointers.Pointer := P;
      --  Copying is free here too, even though the designated value owns a
      --  cell: the cell is reclaimed by the library when the last pointer to
      --  it disappears, so there is no leak to report at the end of scope.
   begin
      pragma Assert (Constant_Reference (P).D /= null);
      pragma Assert (Constant_Reference (P).D.all = 42);
      pragma Assert (Constant_Reference (Q).D.all = 42);
   end Owning;
end Test_Auto_Reclaimed;
