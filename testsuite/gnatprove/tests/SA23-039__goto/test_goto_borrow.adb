procedure Test_Goto_Borrow with SPARK_Mode is
   type List_Cell;
   type List is access List_Cell;
   type List_Cell is record
      Data : Integer;
      Next : List;
   end record;

  function Length (L : access constant List_Cell) return Natural is
   (if L = null then 0
    else Natural'Min (Natural'Last - 1, Length (L.Next)) + 1)
  with Annotate => (GNATprove, Terminating);

  function Nth (L : access constant List_Cell; N : Positive) return Integer is
   (if N = 1 then L.Data else Nth (L.Next, N - 1))
  with Annotate => (GNATprove, Terminating),
    Pre => N <= Length (L);

   function At_End_Borrow (L : access constant List_Cell) return access constant List_Cell is
     (L)
   with Ghost,
     Annotate => (GNATprove, At_End_Borrow);

   procedure Truncate_After_V (L : access List_Cell; Rest : out List; V : Integer; I : out Natural) with
     Pre  => Length (L) < Natural'Last,
     Post => Length (L) = I
     and (if Length (L) /= Length (L)'Old then Nth (L, I) = V)
   is
   begin
      declare
         D : access List_Cell := L;
      begin
         I := 0;
         Rest := null;
         while D /= null loop
            pragma Loop_Invariant (Rest = null);
            pragma Loop_Invariant (I = Length (D)'Loop_Entry - Length (D));
            pragma Loop_Invariant
              (Length (At_End_Borrow (L)) = I + Integer'Min (Length (At_End_Borrow (D)), Natural'Last - I));
            pragma Loop_Invariant
              (for all K in I + 1 .. Length (At_End_Borrow (L)) =>
                 Nth (At_End_Borrow (D), K - I) = Nth (At_End_Borrow (L), K));
            pragma Loop_Invariant
              (for all K in 1 .. Integer'Min (Length (At_End_Borrow (D)), Natural'Last - I) =>
                   Nth (At_End_Borrow (D), K) = Nth (At_End_Borrow (L), K + I));

            I := I + 1;

            if D.Data = V then
               Rest := D.Next;
               D.Next := null;
               goto EEnd;
            end if;
            D := D.Next;
         end loop;
      end;
      pragma Assert (Length (L) = I);
  <<EEnd>>
   end Truncate_After_V;
begin
   null;
end Test_Goto_Borrow;
