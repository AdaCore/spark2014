package body Queen with SPARK_Mode is

   procedure Add_next (B : in out Board; I : Index;
                       Done : in out Boolean; C : in Board)
   is
   begin
      if Consistent (B, I) then
         if N = I then
            Done := True;
         else
            Try_Row (B, I + 1, Done, C);
         end if;
         return;
      else
         pragma Assert (not Consistent (C, I));
         pragma Assert (not (for all J in I .. N => Consistent (C, J)));
      end if;
   end Add_next;

   function Copy_Until (B : in Board; I : Index; C : in Board) return Board is
      R : Board := (Index'Range => 1);
   begin
      for J in Index'First .. I loop
         pragma Loop_Invariant
           (for all K in Index'First .. J - 1 => R (K) = B(K));
         R (J) := B (J);
      end loop;
      for J in I + 1 .. Index'Last loop
         pragma Loop_Invariant
           (for all K in Index'First .. I => R (K) = B(K));
         R (J) := C (J);
      end loop;
      return R;
   end Copy_Until;

   procedure Try_Row (B : in out Board; I : Index; Done : in out Boolean;
                      C : in Board)
   is
   begin
      for R in Index'Range loop
         pragma Loop_Invariant
           (not Done and
              (for all J in 1 .. I - 1 => B (J) = B'Loop_Entry (J)) and
                (if C (I) < R then
                       not Consistent (C, N))
           );
         B (I) := R;
         if C (I) = R then
            Add_next (B, I, Done, C);
         else
            Add_next (B, I, Done, Copy_Until (B, I, C));
         end if;
         if Done then
            exit;
         end if;
      end loop;
   end Try_Row;

end Queen;
