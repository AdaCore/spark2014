package body P is
   function Empty_Seq return Seq_Type is (1);

   procedure Include (S : in out Seq_Type; B : Boolean) is
   begin
      S := S * 2 + (if B then 1 else 0);
   end Include;

   function Model (S : Seq_Type) return Sequence is
      L : constant Integer :=
        (if S < 2 then 0
         elsif S < 4 then 1
         elsif S < 8 then 2
         elsif S < 16 then 3
         elsif S < 32 then 4
         elsif S < 64 then 5
         elsif S < 128 then 6
         else 7);
   begin
      return M : Sequence do
         for I in 1 .. L loop
            M := Add (M, Shift_Right (S, L - I) mod 2 = 1);
            pragma Loop_Invariant (Last (M) = I);
            pragma Loop_Invariant
              (for all K in 1 .. I =>
                 Get (M, K) = (Shift_Right (S, L - K) mod 2 = 1));
         end loop;
      end return;
   end Model;
end;
