package body Use_Vectors
  with SPARK_Mode
is
   function Create return Sequence is
      S : Sequence;
   begin
      for K in 1 .. 42 loop
         S := Add (S, K);
         pragma Loop_Invariant (Integer (Length (S)) = K);
         pragma Loop_Invariant
           (for all J in 1 .. K => Get (S, J) = J);
      end loop;
      return S;
   end Create;

end Use_Vectors;
