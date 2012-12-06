package body Queen is

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

   procedure Try_Row (B : in out Board; I : Index; Done : in out Boolean;
                      C : in Board)
   is
   begin
      for R in Index'Range loop
         pragma Loop_Invariant
           (not Done and
              (for all J in 1 .. I - 1 => B (J) = B'Loop_Entry (J)) and
              (if C (I) < R then
                not (for all J in I .. N => Consistent (C, J)))
           );
         B (I) := R;
         if C (I) = R then
            Add_next (B, I, Done, C);
         else Add_next (B, I, Done, B);
         end if;
         if Done then
            exit;
         end if;
      end loop;
   end Try_Row;

end Queen;
