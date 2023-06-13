with Ada.Numerics.Big_Numbers.Big_Integers;
use Ada.Numerics.Big_Numbers.Big_Integers;

package body List_Mod_Allocator with
  SPARK_Mode,
  Refined_State => (State => (Data, First_Available))
is
   package Big_From_Resource is new Signed_Conversions
     (Int => Resource);
     
   function Big (R : Resource) return Big_Integer renames
     Big_From_Resource.To_Big_Integer;

   type Status is (Available, Allocated);

   type Cell is record
      Stat : Status;
      Next : Resource;
   end record;

   type A is array (Valid_Resource) of Cell;

   Data : A := (others => Cell'(Stat => Available, Next => No_Resource));
   First_Available : Resource := 1;

   function Is_Available (Res : Resource) return Boolean is
     (Res = No_Resource or else Data (Res).Stat = Available);
   function Is_Allocated (Res : Resource) return Boolean is
     (Res = No_Resource or else Data (Res).Stat = Allocated);
   function All_Available return Boolean is
     (for all R in Valid_Resource => Data (R).Stat = Available);

   package body M is

      function Is_Well_Formed return Boolean is
        ((if First_Available /= No_Resource then
               Data (First_Available).Stat = Available)
         and then (for all R in Valid_Resource =>
                     (if Data (R).Stat = Available and then Data (R).Next /= No_Resource
                      then Data (Data (R).Next).Stat = Available)));
      --  The Is_Well_Formed property is the part of the validity function
      --  which can be expressed without refering to the model of the
      --  allocator. In particular it does not included anything that would
      --  need a reachability predicate on available cells.

      function Model_Is_Well_Formed (M : T) return Boolean is
        (declare
            Avail : constant Sequence := M.Available;
            Alloc : constant S2.Set := M.Allocated;
         begin
            Length (Avail) <= Capacity
            and then
              (if First_Available /= No_Resource then
                    Length (Avail) > 0 and then Get (Avail, 1) = First_Available
               else Length (Avail) = 0)
            and then
              (for all J in 1 .. Integer (Last (Avail)) =>
                    Get (Avail, J) in Valid_Resource
               and then
                 (if J < Integer (Last (Avail)) then
                       Data (Get (Avail, J)).Next = Get (Avail, J + 1)))
            and then
              (for all J in 1 .. Last (Avail) =>
                   (if J > 1 then
                         Get (Avail, J - 1) in Valid_Resource
                       and then  Get (Avail, J) = Data (Get (Avail, J - 1)).Next))
            and then
              (for all J in 1 .. Last (Avail) =>
                   (for all K in 1 .. Last (Avail) =>
                        (if Get (Avail, J) = Get (Avail, K) then J = K)))
            and then (if First_Available /= No_Resource
                      and then Data (Get (Avail, Last (Avail))).Next in Valid_Resource
                      then Contains (Avail, Data (Get (Avail, Last (Avail))).Next))
            and then
              (for all E of Alloc => E in Valid_Resource)
            and then (for all R in Valid_Resource =>
                          (case Data (R).Stat is
                              when Available => not Contains (Alloc, R),
                              when Allocated => not Contains (Avail, R) and Contains (Alloc, R))));
      --  If the allocator is well-formed, then its model is well-formed
      --  following this definition. In particular, the list of available cells
      --  is allowed to be cyclic or incomplete, that is, not to contain every
      --  available cell.

      function Model return T is
         Avail  : Sequence;
         Alloc  : S2.Set;
         Unseen : S2.Set;
         --  Unseen is used to bound the length of the Avail sequence in the
         --  second loop. It is computed to be the set of every available
         --  cell in the allocator.

      begin
         for R in Valid_Resource loop
            pragma Loop_Invariant
              (for all E of Alloc => E in 1 .. R - 1);
            pragma Loop_Invariant
              (for all E of Unseen => E in 1 .. R - 1);
            pragma Loop_Invariant
              (for all E in Valid_Resource =>
                 (if Data (E).Stat = Available then not Contains (Alloc, E)));
            pragma Loop_Invariant
              (for all E in 1 .. R - 1 =>
                 (if Data (E).Stat = Allocated then Contains (Alloc, E)
                  else Contains (Unseen, E)));
            pragma Loop_Invariant (Length (Alloc) <= Big (R - 1));
            pragma Loop_Invariant (Length (Unseen) <= Big (R - 1));
            if Data (R).Stat = Allocated then
               Alloc := Add (Alloc, R);
            else
               Unseen := Add (Unseen, R);
            end if;
         end loop;

         declare
            R : Resource := First_Available;
         begin
            while R /= No_Resource and not Contains (Avail, R) loop
               Unseen := Remove (Unseen, R);
               Avail := Add (Avail, R);
               R := Data (R).Next;

               pragma Loop_Variant (Increases => Last (Avail));
               pragma Loop_Invariant (Length (Unseen) <= To_Big_Integer (Capacity));
               pragma Loop_Invariant (Length (Avail) <= To_Big_Integer (Capacity) - Length (Unseen));
               pragma Loop_Invariant
                 (for all E in Valid_Resource =>
                    (if Data (E).Stat = Available and then not Contains (Avail, E)
                    then Contains (Unseen, E)));
               pragma Loop_Invariant
                 (Length (Avail) > 0 and then Get (Avail, 1) = First_Available);
               pragma Loop_Invariant
                 (for all J in 1 .. Last (Avail) =>
                    Get (Avail, J) in Valid_Resource);
               pragma Loop_Invariant
                 (R = Data (Get (Avail, Last (Avail))).Next);
               pragma Loop_Invariant
                 (for all J in 1 .. Last (Avail) - 1 =>
                          Data (Get (Avail, J)).Next = Get (Avail, J + 1));
               pragma Loop_Invariant
                 (for all J in 2 .. Last (Avail) =>
                    Get (Avail, J) = Data (Get (Avail, J - 1)).Next);
               pragma Loop_Invariant
                 (for all J in 1 .. Last (Avail) =>
                    (for all K in 1 .. Last (Avail) =>
                         (if Get (Avail, J) = Get (Avail, K) then J = K)));
               pragma Loop_Invariant
                 (for all E in Valid_Resource =>
                    (if Data (E).Stat = Allocated then not Contains (Avail, E)));
            end loop;
         end;

         --  Part of the Model_Is_Well_Formed predicate which is repeated here
         --  to help the provers with the postcondition
         pragma Assert (for all R in Valid_Resource =>
                          (case Data (R).Stat is
                              when Available => not Contains (Alloc, R),
                              when Allocated => not Contains (Avail, R) and Contains (Alloc, R)));
         return T'(Available => Avail, Allocated => Alloc);
      end Model;

      function Is_Valid return Boolean is
        (Is_Well_Formed
         and then
         (if First_Available /= No_Resource then
            Data (Get (Model.Available, Last (Model.Available))).Next = No_Resource)
         and then
           (for all R in Valid_Resource =>
                (if Data (R).Stat = Available then Contains (Model.Available, R))));
      --  Is_Valid completes Is_Well_Formed by adding properties relative to
      --  reachability of the free list which can only be expressed on the
      --  model of the allocator.

   end M;

   procedure Prove_Is_Preprend (S1, S2 : Sequence) with Ghost
   --  This function proves by induction that S2 is S1 with one more element at
   --  the beginning. It is inlined at call site.

   is
   begin
      for I in 1 .. Last (S1) loop
         pragma Loop_Invariant
           (Last (S2) >= I + 1);
         pragma Loop_Invariant
           (for all J in 1 .. I =>
              Get (S1, J) = Get (S2, J + 1));
         pragma Loop_Invariant
           (for all J in 2 .. I + 1 =>
              Get (S1, J - 1) = Get (S2, J));
      end loop;
      if 1 <= Last (S1) then
         pragma Assert (for all J in 1 .. Last (S1) + 1 =>
                          Get (S2, J) /= Data (Get (S1, Last (S1))).Next);
      end if;
   end Prove_Is_Preprend;

   procedure Alloc (Res : out Resource) is
      Next_Avail : Resource;
      MA : constant Sequence := Model.Available with Ghost;
   begin
      if First_Available /= No_Resource then
         Res := First_Available;
         Next_Avail := Data (First_Available).Next;
         Data (Res) := Cell'(Stat => Allocated, Next => No_Resource);
         First_Available := Next_Avail;

         pragma Assert
           (for all R in Valid_Resource =>
              (if Data (R).Stat = Available and then Data (R).Next /= No_Resource
               then Data (Data (R).Next).Stat = Available));
         Prove_Is_Preprend (Model.Available, MA);
      else
         Res := No_Resource;
      end if;
   end Alloc;

   procedure Free (Res : Resource) is
      MA : constant Sequence := Model.Available with Ghost;
   begin
      if Res /= No_Resource and then Data (Res).Stat = Allocated then
         Data (Res) := Cell'(Stat => Available, Next => First_Available);
         First_Available := Res;

         Prove_Is_Preprend (MA, Model.Available);
      end if;
   end Free;

   procedure Prove_Init (S : Sequence) with Ghost
   --  This function proves by induction that S contains every valid ressource
   --  in increasing order. It is inlined at call site.

   is
   begin
      for I in 1 .. Last (S) loop
         pragma Loop_Invariant
           (for all J in 1 .. I => Get (S, J) = Valid_Resource (J));
      end loop;
   end Prove_Init;

begin
   for R in Valid_Resource loop
      if R < Capacity then Data (R).Next := R + 1; end if;
      pragma Loop_Invariant
        (for all RR in 1 .. R =>
           Data (RR).Next = (if RR = Capacity then No_Resource else RR + 1));
      pragma Loop_Invariant (Data (Capacity).Next = No_Resource);
      pragma Loop_Invariant (for all RR in Valid_Resource => Data (RR).Stat = Available);
   end loop;

   Prove_Init (Model.Available);
   pragma Assert
     (Data (Get (Model.Available, Last (Model.Available))).Next = No_Resource);
   pragma Assert
     (for all R in Valid_Resource => (Contains (Model.Available, R)));
end List_Mod_Allocator;
