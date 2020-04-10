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

   function Pledge (L : access constant List_Cell; P : Boolean) return Boolean is
     (P)
   with Ghost,
     Annotate => (GNATprove, Pledge);

   procedure Truncate_After_V (L : access List_Cell; V : Integer; I : out Natural) with
     Pre  => Length (L) < Natural'Last,
     Post => Length (L) = I
     and (if Length (L) /= Length (L)'Old then Nth (L, I) = V)
   is
   begin
      declare
         D : access List_Cell := L;
      begin
         I := 0;
         while D /= null loop
            pragma Loop_Invariant (I = Length (D)'Loop_Entry - Length (D));
            pragma Loop_Invariant
              (Pledge (D, Length (L) = I + Integer'Min (Length (D), Natural'Last - I)));
            pragma Loop_Invariant
              (Pledge (D, (for all K in I + 1 .. Length (L) => Nth (D, K - I) = Nth (L, K))));
            pragma Loop_Invariant
              (Pledge (D, (for all K in 1 .. Integer'Min (Length (D), Natural'Last - I) => Nth (D, K) = Nth (L, K + I))));

            I := I + 1;

            if D.Data = V then
               pragma Assert (Nth (D, 1) = V);
               D.Next := null;
               pragma Assert (Length (D) = 1);
               goto EEnd;
            end if;
            D := D.Next;
         end loop;
      end;
      <<EEnd>>
   end Truncate_After_V;
begin
   null;
end Test_Goto_Borrow;
