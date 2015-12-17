package body List_Allocator with
  SPARK_Mode,
  Refined_State => (State => (Data, First_Available, First_Allocated))
is
   type Status is (Available, Allocated);

   type Cell is record
      Stat       : Status;
      Prev, Next : Resource;
   end record;

   type A is array (Valid_Resource) of Cell;

   Data : A := (others => Cell'(Stat => Available, Prev => No_Resource, Next => No_Resource));
   First_Available : Resource := 1;
   First_Allocated : Resource := No_Resource;

   function Is_Available (Res : Resource) return Boolean is
     (Res = No_Resource or else Data (Res).Stat = Available);
   function Is_Allocated (Res : Resource) return Boolean is
     (Res = No_Resource or else Data (Res).Stat = Allocated);
   function All_Available return Boolean is
     (for all R in Valid_Resource => Data (R).Stat = Available);

   package body M is

      function Is_Valid return Boolean is
        ((if First_Available /= No_Resource then
            Length (Model.Available) > 0 and then Get (Model.Available, 1) = First_Available
          else
            Length (Model.Available) = 0)
            and then
         (if First_Allocated /= No_Resource then
            Length (Model.Allocated) > 0 and then Get (Model.Allocated, 1) = First_Allocated
          else
            Length (Model.Allocated) = 0)
            and then
         (for all J in 1 .. Length (Model.Available) =>
            Get (Model.Available, J) in Valid_Resource
              and then
            Data (Get (Model.Available, J)).Next =
              (if J < Length (Model.Available) then Get (Model.Available, J + 1) else No_Resource)
              and then
            Data (Get (Model.Available, J)).Prev =
              (if J > 1 then Get (Model.Available, J - 1) else No_Resource)
              and then
            (for all K in 1 .. Length (Model.Available) =>
               (if J /= K then Get (Model.Available, J) /= Get (Model.Available, K))))
            and then
         (for all J in 1 .. Length (Model.Allocated) =>
            Get (Model.Allocated, J) in Valid_Resource
              and then
            Data (Get (Model.Allocated, J)).Next =
              (if J < Length (Model.Allocated) then Get (Model.Allocated, J + 1) else No_Resource)
              and then
            Data (Get (Model.Allocated, J)).Prev =
              (if J > 1 then Get (Model.Allocated, J - 1) else No_Resource)
              and then
            (for all K in 1 .. Length (Model.Allocated) =>
               (if J /= K then Get (Model.Allocated, J) /= Get (Model.Allocated, K))))
            and then
         (for all R in Valid_Resource =>
            (case Data (R).Stat is
               when Available => Mem (Model.Available, R) and not Mem (Model.Allocated, R),
               when Allocated => not Mem (Model.Available, R) and Mem (Model.Allocated, R))));

      function Find (S : Sequence; R : Resource) return Natural is
      begin
         for J in 1 .. Length (S) loop
            if Get (S, J) = R then
               return J;
            end if;
            pragma Loop_Invariant (for all K in 1 .. J => Get (S, K) /= R);
         end loop;
         return 0;
      end Find;

   begin
      for R in Valid_Resource loop
         Model.Available := Add (Model.Available, R);
         pragma Loop_Invariant (for all RR in 1 .. R => Mem (Model.Available, RR));
         pragma Loop_Invariant (Length (Model.Allocated) = 0);
      end loop;
   end M;

   procedure Alloc (Res : out Resource) is
      Next_Avail : Resource;
      MA : Sequence := Model.Available;
   begin
      if First_Available /= No_Resource then
         Res := First_Available;
         Next_Avail := Data (First_Available).Next;

         Data (Res) := Cell'(Stat => Allocated,
                             Prev => No_Resource,
                             Next => First_Allocated);
         if Next_Avail /= No_Resource then
            Data (Next_Avail).Prev := No_Resource;
         end if;
         if First_Allocated /= No_Resource then
            Data (First_Allocated).Prev := First_Available;
         end if;
         First_Allocated := First_Available;
         First_Available := Next_Avail;

         Model.Available := Remove_At (Model.Available, 1);
         Model.Allocated := Prepend (Model.Allocated, Res);

--          pragma Assert
--           (for all R in Valid_Resource =>
--              (if Data (R).Stat = Available then Mem (Model.Available, R)));
--
--          pragma Assert
--           (for all R in Valid_Resource =>
--              (if Data (R).Stat = Available then not Mem (Model.Allocated, R)));

--          pragma Assert
--           (for all R in Valid_Resource =>
--              (if Data (R).Stat = Available then Mem (Model.Available, R) and not Mem (Model.Allocated, R)));
--
--          pragma Assert
--           (for all R in Valid_Resource =>
--              (if Data (R).Stat = Allocated then not Mem (Model.Available, R)));
--
--          pragma Assert (Mem (Model.Allocated, Res));

--          pragma Assert
--           (for all R in Valid_Resource =>
--              (if R /= Res and Data (R).Stat = Allocated then Mem (Model.Allocated, R)));

--          pragma Assert
--           (for all R in Valid_Resource =>
--              (if Data (R).Stat = Allocated then Mem (Model.Allocated, R)));

--          pragma Assert
--           (for all R in Valid_Resource =>
--              (if Data (R).Stat = Allocated then not Mem (Model.Available, R) and Mem (Model.Allocated, R)));

--          pragma Assert
--           (for all R in Valid_Resource =>
--              (case Data (R).Stat is
--                 when Available => Mem (Model.Available, R) and not Mem (Model.Allocated, R),
--                 when Allocated => not Mem (Model.Available, R) and Mem (Model.Allocated, R)));

--           pragma Assert (for all J in 1 .. Length (Model.Available) =>
--              Get (Model.Available, J) in Valid_Resource
--                and then
--              Data (Get (Model.Available, J)).Next =
--                (if J < Length (Model.Available) then Get (Model.Available, J + 1) else No_Resource)
--                and then
--              Data (Get (Model.Available, J)).Prev =
--                (if J > 1 then Get (Model.Available, J - 1) else No_Resource)
--                and then
--              (for all K in 1 .. Length (Model.Available) =>
--                 (if J /= K then Get (Model.Available, J) /= Get (Model.Available, K))));

--           pragma Assert
--           (for all J in 1 .. Length (Model.Allocated) =>
--              Get (Model.Allocated, J) in Valid_Resource
--                and then
--              Data (Get (Model.Allocated, J)).Next =
--                (if J < Length (Model.Allocated) then Get (Model.Allocated, J + 1) else No_Resource)
--                and then
--              Data (Get (Model.Allocated, J)).Prev =
--                (if J > 1 then Get (Model.Allocated, J - 1) else No_Resource)
--                and then
--              (for all K in 1 .. Length (Model.Allocated) =>
--                 (if J /= K then Get (Model.Allocated, J) /= Get (Model.Allocated, K))));

--          pragma Assert (
--            (for all J in 1 .. Length (Model.Available) =>
--              Data (Get (Model.Available, J)) = Data (Get (MA, J + 1))));
--
--          pragma Assert (
--            (for all J in 1 .. Length (MA) - 2 =>
--              Data (Get (MA, J + 1)).Next = Get (MA, J + 2)));
--
--          pragma Assert (
--            (for all J in 1 .. Length (Model.Available) - 1 =>
--              Data (Get (MA, J + 1)).Next = Get (MA, J + 2)));
--
--          pragma Assert (
--            (for all J in 1 .. Length (Model.Available) =>
--              Data (Get (MA, J + 1)).Next =
--                (if J < Length (Model.Available) then Get (MA, J + 2) else No_Resource)));

--          pragma Assert (
--            (for all J in 1 .. Length (Model.Available) =>
--              Data (Get (Model.Available, J)).Next =
--                (if J < Length (Model.Available) then Get (MA, J + 2) else No_Resource)));
--
--          pragma Assert (
--            (for all J in 1 .. Length (Model.Available) =>
--              Get (Model.Available, J) in Valid_Resource
--                and then
--              Data (Get (Model.Available, J)).Next =
--                (if J < Length (Model.Available) then Get (Model.Available, J + 1) else No_Resource)));
--
--          pragma Assert
--           (for all J in 1 .. Length (Model.Allocated) =>
--              Get (Model.Allocated, J) in Valid_Resource);
--
--          pragma Assert
--           (for all J in 1 .. Length (Model.Allocated) =>
--              Get (Model.Allocated, J) in Valid_Resource
--                and then
--              Data (Get (Model.Allocated, J)).Next =
--                (if J < Length (Model.Allocated) then Get (Model.Allocated, J + 1) else No_Resource));

--          pragma Assert ((if First_Available /= No_Resource then
--              Length (Model.Available) > 0 and then Get (Model.Available, 1) = First_Available
--            else
--              Length (Model.Available) = 0)
--              and then
--           (if First_Allocated /= No_Resource then
--              Length (Model.Allocated) > 0 and then Get (Model.Allocated, 1) = First_Allocated
--            else
--              Length (Model.Allocated) = 0)
--              and then
--           (for all J in 1 .. Length (Model.Available) =>
--              Get (Model.Available, J) in Valid_Resource
--                and then
--              Data (Get (Model.Available, J)).Next =
--                (if J < Length (Model.Available) then Get (Model.Available, J + 1) else No_Resource))
--              and then
--           (for all J in 1 .. Length (Model.Allocated) =>
--              Get (Model.Allocated, J) in Valid_Resource
--                and then
--              Data (Get (Model.Allocated, J)).Next =
--                (if J < Length (Model.Allocated) then Get (Model.Allocated, J + 1) else No_Resource))
--              and then
--           (for all R in Valid_Resource =>
--              (case Data (R).Stat is
--                 when Available => Mem (Model.Available, R) and not Mem (Model.Allocated, R),
--                 when Allocated => not Mem (Model.Available, R) and Mem (Model.Allocated, R))));

      else
         Res := No_Resource;
      end if;
   end Alloc;

   procedure Free (Res : Resource) is
      Prev_Alloc, Next_Alloc : Resource;
   begin
      if Res /= No_Resource and then Data (Res).Stat = Allocated then
         Prev_Alloc := Data (Res).Prev;
         Next_Alloc := Data (Res).Next;

         Data (Res) := Cell'(Stat => Available,
                             Prev => No_Resource,
                             Next => First_Available);
         if Prev_Alloc /= No_Resource then
            Data (Prev_Alloc).Next := Next_Alloc;
         end if;
         if Next_Alloc /= No_Resource then
            Data (Next_Alloc).Prev := Prev_Alloc;
         end if;
         if First_Available /= No_Resource then
            Data (First_Available).Prev := Res;
         end if;
         First_Available := Res;
         if Res = First_Allocated then
            First_Allocated := Next_Alloc;
         end if;

         Model.Allocated := Remove_At (Model.Allocated, Find (Model.Allocated, Res));
         Model.Available := Prepend (Model.Available, Res);

         pragma Assert (
          (for all J in 1 .. Length (Model.Available) =>
            Get (Model.Available, J) in Valid_Resource
              and then
            Data (Get (Model.Available, J)).Next =
              (if J < Length (Model.Available) then Get (Model.Available, J + 1) else No_Resource)));

--          pragma Assert
--           (for all J in 1 .. Length (Model.Allocated) =>
--              Get (Model.Allocated, J) in Valid_Resource);

--          pragma Assert
--           (for all J in 1 .. Length (Model.Allocated) =>
--              Get (Model.Allocated, J) in Valid_Resource
--                and then
--              Data (Get (Model.Allocated, J)).Next =
--                (if J < Length (Model.Allocated) then Get (Model.Allocated, J + 1) else No_Resource));


--           pragma Assert (Data (Get (Model.Available, 1)).Prev = No_Resource);
--           pragma Assert (if Length (Model.Available) > 1 then Data (Get (Model.Available, 2)).Prev = Get (Model.Available, 1));
--
--           pragma Assert (for all J in 2 .. Length (Model.Available) =>
--              Data (Get (Model.Available, J)).Prev = Get (Model.Available, J - 1));
--
--           pragma Assert (for all J in 1 .. Length (Model.Available) =>
--              Data (Get (Model.Available, J)).Prev =
--                (if J > 1 then Get (Model.Available, J - 1) else No_Resource));
--
--           pragma Assert (for all J in 1 .. Length (Model.Available) =>
--              (for all K in 1 .. Length (Model.Available) =>
--                 (if J /= K then Get (Model.Available, J) /= Get (Model.Available, K))));

--           pragma Assert (for all J in 1 .. Length (Model.Available) =>
--              Get (Model.Available, J) in Valid_Resource
--                and then
--              Data (Get (Model.Available, J)).Next =
--                (if J < Length (Model.Available) then Get (Model.Available, J + 1) else No_Resource)
--                and then
--              Data (Get (Model.Available, J)).Prev =
--                (if J > 1 then Get (Model.Available, J - 1) else No_Resource)
--                and then
--              (for all K in 1 .. Length (Model.Available) =>
--                 (if J /= K then Get (Model.Available, J) /= Get (Model.Available, K))));

         pragma Assert
         (for all J in 1 .. Length (Model.Allocated) =>
            Get (Model.Allocated, J) in Valid_Resource
              and then
            Data (Get (Model.Allocated, J)).Next =
              (if J < Length (Model.Allocated) then Get (Model.Allocated, J + 1) else No_Resource)
              and then
            Data (Get (Model.Allocated, J)).Prev =
              (if J > 1 then Get (Model.Allocated, J - 1) else No_Resource)
              and then
            (for all K in 1 .. Length (Model.Allocated) =>
               (if J /= K then Get (Model.Allocated, J) /= Get (Model.Allocated, K))));

--          pragma Assert (Mem (Model.Available, Res));
--
--          pragma Assert
--           (for all R in Valid_Resource =>
--              (if R /= Res and Data (R).Stat = Available then Mem (Model.Available, R)));

--          pragma Assert
--           (for all R in Valid_Resource =>
--              (if Data (R).Stat = Available then Mem (Model.Available, R)));
--
--          pragma Assert
--           (for all R in Valid_Resource =>
--              (if Data (R).Stat = Available then not Mem (Model.Allocated, R)));

--          pragma Assert
--           (for all R in Valid_Resource =>
--              (if Data (R).Stat = Available then Mem (Model.Available, R) and not Mem (Model.Allocated, R)));

--          pragma Assert
--           (for all R in Valid_Resource =>
--              (if Data (R).Stat = Allocated then not Mem (Model.Available, R)));

--          pragma Assert
--           (for all R in Valid_Resource =>
--              (if Data (R).Stat = Allocated then Mem (Model.Allocated, R)));

--          pragma Assert
--           (for all R in Valid_Resource =>
--              (if Data (R).Stat = Allocated then not Mem (Model.Available, R) and Mem (Model.Allocated, R)));

--          pragma Assert
--           (for all R in Valid_Resource =>
--              (case Data (R).Stat is
--                 when Available => Mem (Model.Available, R) and not Mem (Model.Allocated, R),
--                 when Allocated => not Mem (Model.Available, R) and Mem (Model.Allocated, R)));

--          pragma Assert ((if First_Available /= No_Resource then
--              Length (Model.Available) > 0 and then Get (Model.Available, 1) = First_Available
--            else
--              Length (Model.Available) = 0)
--              and then
--           (if First_Allocated /= No_Resource then
--              Length (Model.Allocated) > 0 and then Get (Model.Allocated, 1) = First_Allocated
--            else
--              Length (Model.Allocated) = 0)
--              and then
--           (for all J in 1 .. Length (Model.Available) =>
--              Get (Model.Available, J) in Valid_Resource
--                and then
--              Data (Get (Model.Available, J)).Next =
--                (if J < Length (Model.Available) then Get (Model.Available, J + 1) else No_Resource))
--              and then
--           (for all J in 1 .. Length (Model.Allocated) =>
--              Get (Model.Allocated, J) in Valid_Resource
--                and then
--              Data (Get (Model.Allocated, J)).Next =
--                (if J < Length (Model.Allocated) then Get (Model.Allocated, J + 1) else No_Resource))
--              and then
--           (for all R in Valid_Resource =>
--              (case Data (R).Stat is
--                 when Available => Mem (Model.Available, R) and not Mem (Model.Allocated, R),
--                 when Allocated => not Mem (Model.Available, R) and Mem (Model.Allocated, R))));
      end if;
   end Free;

begin
   for R in Valid_Resource loop
      if R > 1 then Data (R).Prev := R - 1; end if;
      if R < Capacity then Data (R).Next := R + 1; end if;
      pragma Loop_Invariant
        (for all RR in 1 .. R =>
           Data (RR).Prev = (if RR = 1 then No_Resource else RR - 1));
      pragma Loop_Invariant
        (for all RR in 1 .. R =>
           Data (RR).Next = (if RR = Capacity then No_Resource else RR + 1));
      pragma Loop_Invariant (Data (Capacity).Next = No_Resource);
      pragma Loop_Invariant (for all RR in Valid_Resource => Data (RR).Stat = Available);
   end loop;
end List_Allocator;
