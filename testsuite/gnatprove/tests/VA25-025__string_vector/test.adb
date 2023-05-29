with SPARK.Containers.Functional.Vectors;

procedure Test with SPARK_Mode is
   procedure Regular_String_Eq with
     Global => null
   is
      package My_Seqs is new SPARK.Containers.Functional.Vectors (Positive, String);

      S : My_Seqs.Sequence;
   begin
      S := My_Seqs.Add (S, "toto");
      S := My_Seqs.Add (S, "tata");
      S := My_Seqs.Add (S, "titi");
      S := My_Seqs.Add (S, "    ");
      S := My_Seqs.Add (S, "    ");
      S := My_Seqs.Add (S, "    ");
      S := My_Seqs.Add (S, "    ");
      pragma Assert (My_Seqs.Get (S, 1) = "toto");
      pragma Assert (My_Seqs.Get (S, 2) = "tata");
      pragma Assert (My_Seqs.Get (S, 3) = "titi");
      pragma Assert (for all E of S => E'First = 1);
      pragma Assert (for all E of S => E'Last = 4);
   end Regular_String_Eq;

   function My_Eq (L, R : String) return Boolean is
     (L = R and L'First = R'First);

   procedure String_Eq_With_First with
     Global => null
   is
      package My_Seqs is new SPARK.Containers.Functional.Vectors (Positive, String, My_Eq);

      S : My_Seqs.Sequence;
   begin
      S := My_Seqs.Add (S, "toto");
      S := My_Seqs.Add (S, "tata");
      S := My_Seqs.Add (S, "titi");
      S := My_Seqs.Add (S, "    ");
      S := My_Seqs.Add (S, "    ");
      S := My_Seqs.Add (S, "    ");
      S := My_Seqs.Add (S, "    ");
      pragma Assert (My_Seqs.Get (S, 1) = "toto");
      pragma Assert (My_Seqs.Get (S, 2) = "tata");
      pragma Assert (My_Seqs.Get (S, 3) = "titi");
      pragma Assert (for all E of S => E'First = 1);
      pragma Assert (for all E of S => E'Last = 4);
   end String_Eq_With_First;
begin
   null;
end Test;
