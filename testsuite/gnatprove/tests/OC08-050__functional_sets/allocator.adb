package body Allocator with
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

   package body M with
     Annotate => (GNATprove, Unhide_Info, "Package_Body")
   is

      function Is_Valid (M : T) return Boolean is
        ((for all E in M.Available => E in Valid_Resource)
            and then
         (for all E in M.Allocated => E in Valid_Resource)
            and then
         (for all R in Valid_Resource =>
            (case Data (R) is
               when Available => Mem (M.Available, R) and not Mem (M.Allocated, R),
               when Allocated => not Mem (M.Available, R) and Mem (M.Allocated, R))));

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
              ((for all E in Avail => E in 1 .. R)
                  and then
               (for all E in Alloc => E in 1 .. R)
                  and then
               (for all RR in 1 .. R =>
                 (case Data (RR) is
                    when Available => Mem (Avail, RR) and not Mem (Alloc, RR),
                    when Allocated => not Mem (Avail, RR) and Mem (Alloc, RR))));
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

end Allocator;
