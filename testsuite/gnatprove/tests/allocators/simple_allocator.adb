with Ada.Containers; use type Ada.Containers.Count_Type;

package body Simple_Allocator with
  SPARK_Mode,
  Refined_State => (State => Data)
is
   type Status is (Available, Allocated);

   type A is array (Valid_Resource) of Status;

   Data : A := (others => Available);

   function Is_Available (Res : Resource) return Boolean is
     (Res = No_Resource or else Data (Res) = Available);
   function Is_Allocated (Res : Resource) return Boolean is
     (Res = No_Resource or else Data (Res) = Allocated);
   function All_Available return Boolean is
     (for all R in Valid_Resource => Data (R) = Available);

   package body M is

      function Is_Valid (M : T) return Boolean is
        ((for all E of M.Available => E in Valid_Resource)
            and then
         (for all E of M.Allocated => E in Valid_Resource)
            and then
         (for all R in Valid_Resource =>
            (declare
               In_Avail : constant Boolean := Contains (M.Available, R);
               In_Alloc : constant Boolean := Contains (M.Allocated, R);
             begin
               (case Data (R) is
                   when Available => In_Avail and not In_Alloc,
                   when Allocated => not In_Avail and In_Alloc))));

      function Model return T is
         Avail : Set;
         Alloc : Set;
      begin
         for R in Valid_Resource loop
            case Data (R) is
               when Available => Avail := Add (Avail, R);
               when Allocated => Alloc := Add (Alloc, R);
            end case;
            pragma Loop_Invariant
              (Length (Avail) + Length (Alloc) = Ada.Containers.Count_Type (R)
                  and then
               (for all E of Avail => E in 1 .. R)
                  and then
               (for all E of Alloc => E in 1 .. R)
                  and then
               (for all RR in 1 .. R =>
                 (declare
                    In_Avail : constant Boolean := Contains (Avail, RR);
                    In_Alloc : constant Boolean := Contains (Alloc, RR);
                  begin
                    (case Data (RR) is
                       when Available => In_Avail and not In_Alloc,
                       when Allocated => not In_Avail and In_Alloc))));
         end loop;
         return T'(Available => Avail, Allocated => Alloc);
      end Model;

   end M;

   procedure Alloc (Res : out Resource) is
   begin
      for R in Valid_Resource loop
         if Data (R) = Available then
            Data (R) := Allocated;
            Res := R;
            return;
         end if;
         pragma Loop_Invariant
           (Data = Data'Loop_Entry
            and then (for all RR in 1 .. R => Data (RR) = Allocated));
      end loop;
      Res := No_Resource;
   end Alloc;

   procedure Free (Res : Resource) is
   begin
      if Res /= No_Resource and then Data (Res) = Allocated then
         Data (Res) := Available;
      end if;
   end Free;

end Simple_Allocator;
