package body List_Allocator with
  SPARK_Mode,
  Refined_State => (State => (Data, First_Available))
is
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

      function Is_Valid return Boolean is
       (declare
          Avail : constant Sequence := Model.Available;
          Alloc : constant S2.Set := Model.Allocated;
        begin
          Length (Avail) <= Capacity and then
          Length (Alloc) <= Capacity and then
          Length (Avail) + Length (Alloc) = Capacity and then
          (if First_Available /= No_Resource then
             Length (Avail) > 0 and then Get (Avail, 1) = First_Available
           else
             Length (Avail) = 0)
             and then
          (for all J in 1 .. Integer (Length (Avail)) =>
             Get (Avail, J) in Valid_Resource
               and then
             Data (Get (Avail, J)).Next =
               (if J < Integer (Length (Avail)) then Get (Avail, J + 1) else No_Resource)
               and then
             (for all K in 1 .. J - 1 =>
                Get (Avail, J) /= Get (Avail, K)))
             and then
          (for all E of Alloc => E in Valid_Resource)
             and then
          (for all R in Valid_Resource =>
             (case Data (R).Stat is
                when Available => Contains (Avail, R) and not Contains (Alloc, R),
                when Allocated => not Contains (Avail, R) and Contains (Alloc, R))));

   begin
      pragma Assert (Length (Model.Available) = 0);
      for R in Valid_Resource loop
         Model.Available := Add (Model.Available, R);
         pragma Loop_Invariant (Is_Empty (Model.Allocated));
         pragma Loop_Invariant (Length (Model.Allocated) = 0);
         pragma Loop_Invariant (Integer (Length (Model.Available)) = Natural (R));
         pragma Loop_Invariant (Get (Model.Available, 1) = 1);
         pragma Loop_Invariant
           (for all RR in 1 .. R => Get (Model.Available, Natural (RR)) = RR);
         pragma Loop_Invariant
           (for all RR in 1 .. R => Contains (Model.Available, RR));
      end loop;
      pragma Assert (Length (Model.Available) = Capacity);
   end M;

   procedure Alloc (Res : out Resource) is
      Next_Avail : Resource;
      MA : Sequence := Model.Available with Ghost;
   begin
      if First_Available /= No_Resource then
         Res := First_Available;
         Next_Avail := Data (First_Available).Next;
         Data (Res) := Cell'(Stat => Allocated, Next => No_Resource);
         First_Available := Next_Avail;

         Model.Available := Remove (Model.Available, 1);
         Model.Allocated := Add (Model.Allocated, Res);

         pragma Assert
           (for all J in 1 .. Integer (Length (Model.Available)) =>
              (for all K in 1 .. J - 1 =>
                   Get (Model.Available, J) /= Get (Model.Available, K)));
      else
         Res := No_Resource;
      end if;
   end Alloc;

   procedure Free (Res : Resource) is
   begin
      if Res /= No_Resource and then Data (Res).Stat = Allocated then
         Data (Res) := Cell'(Stat => Available, Next => First_Available);
         First_Available := Res;

         Model.Allocated := Remove (Model.Allocated, Res);
         Model.Available := Add (Model.Available, 1, Res);
      end if;
   end Free;

begin
   for R in Valid_Resource loop
      if R < Capacity then Data (R).Next := R + 1; end if;
      pragma Loop_Invariant
        (for all RR in 1 .. R =>
           Data (RR).Next = (if RR = Capacity then No_Resource else RR + 1));
      pragma Loop_Invariant (Data (Capacity).Next = No_Resource);
      pragma Loop_Invariant (for all RR in Valid_Resource => Data (RR).Stat = Available);
   end loop;
end List_Allocator;
