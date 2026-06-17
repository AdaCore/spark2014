pragma Ada_2022;
pragma Extensions_Allowed (All_Extensions);

with SPARK.Big_Integers; use SPARK.Big_Integers;
with SPARK.Higher_Order.Reachability;
with SPARK.Containers.Functional.Sets;

package body Allocator.Base
  with SPARK_Mode
is
   package Model
     with Ghost
   is
      package Index_Conversions is new Signed_Conversions (Index_Type'Base);
      function Big (X : Index_Type'Base) return Big_Integer
      renames Index_Conversions.To_Big_Integer;

      package Memory_Index_Sets is new
        SPARK.Containers.Functional.Sets (Index_Type);

      function Next (X : Relaxed_Cell) return Extended_Index'Base
      is (if X.C.Next in Index_Type then X.C.Next else 0)
      with Annotate => (GNATprove, Inline_For_Proof), Pre => X.C'Initialized;

      package Node_Reachability is new
        SPARK.Higher_Order.Reachability
          (Index_Type,
           0,
           Relaxed_Cell,
           Init_Memory_Type,
           Next,
           Memory_Index_Sets,
           Memory_Index_Sequences,
           Automatically_Instantiate_Definitions => True);
      use Node_Reachability;

      function All_From (I : Index_Type) return Memory_Index_Sequences.Sequence
      with
        Post               =>
          Memory_Index_Sequences.Length (All_From'Result)
          = Big (Index_Type'Last - I + 1)
          and then
            (for all K in 1 .. Index_Type'Last - I + 1 =>
               Memory_Index_Sequences.Get (All_From'Result, Big (K))
               = Index_Type'Last - K + 1)
          and then
            (for all K in I .. Index_Type'Last =>
               Memory_Index_Sequences.Get
                 (All_From'Result, Big (Index_Type'Last - K + 1))
               = K),
        Subprogram_Variant => (Decreases => Index_Type'Last - I);

   end Model;
   use Model;
   use type Memory_Index_Sets.Set;

   package body Model is

      function All_From (I : Index_Type) return Memory_Index_Sequences.Sequence
      is (Memory_Index_Sequences.Add
            ((if I = Index_Type'Last
              then Memory_Index_Sequences.Empty_Sequence
              else All_From (I + 1)),
             I));

   end Model;

   function Base_Invariant return Boolean
   is (if Free >= 0
       then
         (for all C of Memory => C'Initialized)
         and then Node_Reachability.Is_Acyclic (Free, Memory)
       else (for all I in 1 .. -Free - 1 => Memory (I)'Initialized));

   function Invariant return Boolean
   is (Base_Invariant
       and then
         (if Free > 0
          then
            Memory (Memory_Index_Sequences.Get (Free_Cells, 1)).C.Next = 0));

   function Free_Cells return Memory_Index_Sequences.Sequence
   is (if Free < 0
       then All_From (-Free)
       else Node_Reachability.Model (Free, Memory));

   procedure Prove_Preserved_Free_List (Memory_Old : Memory_Type) with Ghost is
   begin
      if Free > 0 then
         Node_Reachability.Lemma_Is_Acyclic_Preserved
           (Free, Memory_Old, Memory);
         Node_Reachability.Lemma_Reachable_Preserved
           (Free, Memory_Old, Memory);
         Node_Reachability.Lemma_Model_Preserved (Free, Memory_Old, Memory);
      end if;
   end Prove_Preserved_Free_List;

   function Allocated_Cells return Memory_Index_Maps.Map
   with
     Refined_Post =>
         (for all I of Free_Cells => not Has_Key (Allocated_Cells'Result, I))
       and then
         Memory_Index_Sequences.Length (Free_Cells)
         + Memory_Index_Maps.Length (Allocated_Cells'Result)
         = To_Big_Integer (Allocator_length)
       and then
         (if Free < 0
          then
            (for all I in Index_Type =>
               Memory_Index_Maps.Has_Key (Allocated_Cells'Result, I)
               = (I < -Free))
          else
            (for all I in Index_Type =>
               Memory_Index_Maps.Has_Key (Allocated_Cells'Result, I)
               = (not Node_Reachability.Reachable (Free, Memory, I))))
       and then
         (for all I of Allocated_Cells'Result =>
            Memory (I)'Initialized
            and then
              Memory_Index_Maps.Get (Allocated_Cells'Result, I)
              = To_Object (Memory (I).C))
   is
   begin
      return Res : Memory_Index_Maps.Map do
         if Free < 0 then
            for I in 1 .. -Free - 1 loop
               Res := Memory_Index_Maps.Add (Res, I, To_Object (Memory (I).C));
               pragma
                 Loop_Invariant
                   (for all K in 1 .. I => Memory_Index_Maps.Has_Key (Res, K));
               pragma Loop_Invariant (for all K of Res => K in 1 .. I);
               pragma
                 Loop_Invariant
                   (for all I of Res =>
                      Memory_Index_Maps.Get (Res, I)
                      = To_Object (Memory (I).C));
               pragma
                 Loop_Invariant (Memory_Index_Maps.Length (Res) = Big (I));
            end loop;
            pragma
              Assert
                (Memory_Index_Maps.Length (Res)
                 + Big (Index_Type'Last + Free + 1)
                 = Big (Index_Type'Last));
         else
            declare
               F : Memory_Index_Sets.Set :=
                 Node_Reachability.Reachable_Set (Free, Memory);
            begin
               for I in Index_Type loop
                  if Memory_Index_Sets.Contains (F, I) then
                     F := Memory_Index_Sets.Remove (F, I);
                  else
                     Res :=
                       Memory_Index_Maps.Add
                         (Res, I, To_Object (Memory (I).C));
                  end if;
                  pragma Loop_Invariant (F <= F'Loop_Entry);
                  pragma Loop_Invariant (for all K of F => K > I);
                  pragma
                    Loop_Invariant
                      (for all K of F'Loop_Entry =>
                         (if K > I then Memory_Index_Sets.Contains (F, K)));
                  pragma
                    Loop_Invariant
                      (for all K in 1 .. I =>
                         Memory_Index_Sets.Contains (F'Loop_Entry, K)
                         or Memory_Index_Maps.Has_Key (Res, K));
                  pragma
                    Loop_Invariant
                      (for all K of Res =>
                         K in 1 .. I
                         and not Memory_Index_Sets.Contains (F'Loop_Entry, K));
                  pragma
                    Loop_Invariant
                      (for all I of Res =>
                         Memory_Index_Maps.Get (Res, I)
                         = To_Object (Memory (I).C));
                  pragma
                    Loop_Invariant
                      (Memory_Index_Maps.Length (Res)
                       + Memory_Index_Sequences.Length (Node_Reachability.Model (Free, Memory))
                       = Big (I) + Memory_Index_Sets.Length (F));
               end loop;
               pragma Assert (Memory_Index_Sets.Is_Empty (F));
               pragma
                 Assert
                   (Memory_Index_Maps.Length (Res)
                    + Memory_Index_Sequences.Length
                      (Node_Reachability.Model (Free, Memory))
                    = Big (Index_Type'Last));
            end;
         end if;
      end return;
   end Allocated_Cells;

   function Allocate (O : Binary_Object_Type) return Index_Type is
      Memory_Old : constant Memory_Type := Memory
      with Ghost;
   begin
      return Res : Index_Type do
         if Free < 0 then
            Res := -Free;
            if Free = -Index_Type'Last then
               Free := 0;
            else
               Free := Free - 1;
            end if;
         else
            Res := Free;
            Free := Memory (Free).C.Next;
         end if;
         Memory (Res) := (C => From_Object (O));
         Prove_Preserved_Free_List (Memory_Old);
      end return;
   end Allocate;

   procedure Deallocate (I : Index_Type) is

      procedure Prove_Expansion with Ghost is
      begin
         for K in reverse Free .. Index_Type'Last loop
            pragma Loop_Invariant (Node_Reachability.Is_Acyclic (K, Memory));
            pragma
              Loop_Invariant
                (All_From (K) = Node_Reachability.Model (K, Memory));
            pragma
              Loop_Invariant
                (for all L in Index_Type =>
                   Memory_Index_Sets.Contains
                     (Node_Reachability.Reachable_Set (K, Memory), L)
                   = (L >= K));
         end loop;
      end Prove_Expansion;

      Memory_Old          : Memory_Type
      with Ghost;
      Free_Cells_Old      : constant Memory_Index_Sequences.Sequence :=
        Free_Cells
      with Ghost;
      Allocated_Cells_Old : constant Memory_Index_Maps.Map := Allocated_Cells
      with Ghost;
   begin
      if Free < 0 and I = -Free - 1 then
         Free := Free + 1;
      elsif Free = 0 and I = Index_Type'Last then
         Free := -Index_Type'Last;
      else

         --  Expand the free list if necessary

         if Free < 0 then
            Memory (Index_Type'Last).C :=
              (Next => 0, Padding => (others => 0));
            for K in -Free .. Index_Type'Last - 1 loop
               Memory (K).C := (Next => K + 1, Padding => (others => 0));
               pragma
                 Loop_Invariant
                   (for all L in -Free .. K =>
                      Memory (L)'Initialized and Memory (L).C.Next = L + 1);
            end loop;
            Free := -Free;
            Prove_Expansion;
            pragma Assert (Base_Invariant);
            pragma
              Assert_And_Cut
                (Free > 0
                 and Free_Cells = Free_Cells_Old
                 and Allocated_Cells = Allocated_Cells_Old
                 and Invariant
                 and (not Node_Reachability.Reachable (Free, Memory, I)));
         end if;
         Memory_Old := Memory;

         Memory (I).C.Next := Free;
         Prove_Preserved_Free_List (Memory_Old);
         Free := I;

         pragma Assert (Invariant);
         pragma
           Assert
             (for all K of Allocated_Cells =>
                Memory_Index_Maps.Has_Key (Allocated_Cells_Old, K));
         pragma
           Assert (for all K of Allocated_Cells_Old =>
                     K = I or Memory_Index_Maps.Has_Key (Allocated_Cells, K));
      end if;
   end Deallocate;

   function Deref (I : Index_Type) return Binary_Object_Type
   is (To_Object (Memory (I).C));

end Allocator.Base;
