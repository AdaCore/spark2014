with Ada.Unchecked_Deallocation;
with SPARK.Pointers.Poisoned.Pointers;
with SPARK.Pointers.Poisoned.Views;

--  Poisoned holders and views. A poisoned value is one that has been moved
--  out of; it relaxes the ownership policy, which is what makes it possible
--  to move elements around inside an array.

procedure Test_Poisoned with SPARK_Mode is
   pragma Unevaluated_Use_Of_Old (Allow);

   type Index is range 1 .. 10;

   ------------------------------------------------------------------
   --  A designated object subject to ownership, held in a holder.  --
   ------------------------------------------------------------------

   type Int_Acc is access Integer;

   type Owning_Object is record
      D : Int_Acc;
   end record;

   function Is_Reclaimed (X : Owning_Object) return Boolean is (X.D = null)
   with Ghost => Static;

   procedure Free is new Ada.Unchecked_Deallocation (Integer, Int_Acc);

   package Owning_Pointers is new
     SPARK.Pointers.Poisoned.Pointers (Owning_Object, Is_Reclaimed);

   function Make (V : Integer) return Owning_Object
   is (D => new Integer'(V));
   function Create_Owning is new Owning_Pointers.Create (Integer, Make);

   use type Owning_Pointers.Pointer;
   --  Only the operators, so that Pointer itself is not made visible here:
   --  a second Pointers instance below would hide it.

   procedure Reclaim_Owning (H : in out Owning_Pointers.Pointer)
   with
     Pre  => (Static => not Owning_Pointers.Is_Poisoned (H)),
     Post => (Static => H = Owning_Pointers.Null_Pointer)
   is
   begin
      if H /= Owning_Pointers.Null_Pointer then
         declare
            C : access Owning_Object := Owning_Pointers.Reference (H);
         begin
            Free (C.D);
         end;
      end if;
      Owning_Pointers.Reclaim (H);
   end Reclaim_Owning;

   -----------------------------------------------------------------
   --  A plain designated object, for the array operations. There  --
   --  is nothing to free, so reclaiming a holder is just Reclaim. --
   -----------------------------------------------------------------

   type Plain_Object is record
      V : Natural;
   end record;

   package Plain_Pointers is new
     SPARK.Pointers.Poisoned.Pointers (Plain_Object);
   use Plain_Pointers;

   function Id (X : Plain_Object) return Plain_Object is (X);
   function Create_Plain is new Plain_Pointers.Create (Plain_Object, Id);

   package Pointer_Arrays is new Plain_Pointers.Array_Operations (Index);
   use Pointer_Arrays;

   --  Swap two elements of a holder array, going through the poisoned state
   --  that the borrow checker would otherwise reject.

   procedure Swap_Pointers (A : in out Pointer_Array; I, J : Index)
   with
     Pre  =>
       (Static =>
          I in A'Range
          and then J in A'Range
          and then (for all E of A => not Is_Poisoned (E))),
     Post =>
       (Static =>
          (for all E of A => not Is_Poisoned (E))
          and then Extensional_Eq (A (I), Copy (A)'Old (J))
          and then Extensional_Eq (A (J), Copy (A)'Old (I)))
   is
      Temp : Pointer;
   begin
      if I = J then
         return;
      end if;
      Temp := Take (A (I));
      Relocate (A, J, I);
      Move (Temp, A (J));
   end Swap_Pointers;

   ---------------------------------------------------------------
   --  Views of an existing array, rather than allocated cells.  --
   ---------------------------------------------------------------

   package Plain_Views is new
     SPARK.Pointers.Poisoned.Views (Plain_Object);
   use Plain_Views;
   --  Array_Operations names Is_Poisoned in the predicate of Readable_Array, so
   --  the parent instance has to be use-visible where it is instantiated.

   type Object_Array is array (Index range <>) of aliased Plain_Object;
   package View_Arrays is new Plain_Views.Array_Operations
     (Index, Object_Array);

   procedure Swap_Views (A : in out View_Arrays.View_Array; I, J : Index)
   with
     Pre  =>
       (Static =>
          I in A'Range
          and then J in A'Range
          and then (for all E of A => not Is_Poisoned (E))),
     Post =>
       (Static =>
          (for all E of A => not Is_Poisoned (E))
          and then Extensional_Eq (A (I), View_Arrays.Copy (A)'Old (J))
          and then Extensional_Eq (A (J), View_Arrays.Copy (A)'Old (I)))
   is
      use View_Arrays;
      Temp : View;
   begin
      if I = J then
         return;
      end if;
      Temp := Take (A (I));
      Relocate (A, J, I);
      Move (Temp, A (J));
   end Swap_Views;

   procedure Swap (A : aliased in out Object_Array; I, J : Index)
   with Pre => I in A'Range and then J in A'Range
   is
      V : constant not null access View_Arrays.Readable_Array :=
        View_Arrays.Get_View (A);
   begin
      Swap_Views (V.all, I, J);
   end Swap;

begin
   Owning_Pointer :
   declare
      H : Owning_Pointers.Pointer := Create_Owning (42);
      G : Owning_Pointers.Pointer;
   begin
      pragma Assert (Static => Owning_Pointers.Is_Poisoned (H) = False);
      pragma Assert (Owning_Pointers.Constant_Reference (H).D.all = 42);

      --  Taking the content poisons the source

      G := Owning_Pointers.Take (H);
      pragma Assert (Static => Owning_Pointers.Is_Poisoned (H));
      pragma Assert (Static => not Owning_Pointers.Is_Poisoned (G));
      pragma Assert (Owning_Pointers.Constant_Reference (G).D.all = 42);

      Reclaim_Owning (G);
      --  H needs no reclamation: a poisoned holder is already reclaimed as
      --  far as the ownership policy is concerned, and Reclaim would in fact
      --  reject it.
      pragma Assert (Static => Owning_Pointers.Is_Reclaimed (H));
   end Owning_Pointer;

   Pointer_Array_Ops :
   declare
      A : Pointer_Array (1 .. 3) :=
        [Create_Plain ((V => 1)), Create_Plain ((V => 2)),
         Create_Plain ((V => 3))];
   begin
      pragma Assert (Constant_Reference (A (1)).V = 1);
      pragma Assert (Constant_Reference (A (3)).V = 3);
      Swap_Pointers (A, 1, 3);
      pragma Assert (Constant_Reference (A (1)).V = 3);
      pragma Assert (Constant_Reference (A (3)).V = 1);
      for I in A'Range loop
         pragma Loop_Invariant
           (Static => (for all J in I .. A'Last => not Is_Poisoned (A (J))));
         pragma Loop_Invariant
           (Static =>
              (for all J in A'First .. I - 1 => Is_Reclaimed (A (J))));
         Reclaim (A (I));
      end loop;
   end Pointer_Array_Ops;

   View_Array_Ops :
   declare
      A : aliased Object_Array := [(V => 1), (V => 2), (V => 3)];
   begin
      Swap (A, 1, 3);
   end View_Array_Ops;
end Test_Poisoned;
