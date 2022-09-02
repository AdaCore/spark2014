with SPARK.Containers.Functional.Maps;
with SPARK.Containers.Functional.Sets;

procedure Test with SPARK_Mode is

   procedure Test_Maps is
      package Map_Pkg is new SPARK.Containers.Functional.Maps (Natural, Natural);
      use Map_Pkg;

      M : Map;
      K, E : Natural;
   begin
      M := Add (M, 1, 2);
      M := Add (M, 2, 3);
      M := Add (M, 3, 4);
      M := Add (M, 5, 6);

      K := Choose (M);

      pragma Assert (Has_Key (M, K));
      pragma Assert (Get (M, K) = K + 1);

      declare
         Buffer : Map := M;
      begin
         while not Is_Empty (Buffer) loop
            K := Choose (Buffer);

            pragma Assert (Get (Buffer, K) = K + 1);

            Buffer := Remove (Buffer, K);

            pragma Loop_Variant (Decreases => Length (Buffer));
            pragma Loop_Invariant (Buffer <= M);
         end loop;
      end;
   end Test_Maps;

   procedure Test_Set is
      package Set_Pkg is new SPARK.Containers.Functional.Sets (Natural);
      use Set_Pkg;

      S : Set;
      E : Natural;
   begin
      S := Add (S, 1);
      S := Add (S, 2);
      S := Add (S, 3);

      E := Choose (S);

      pragma Assert (Contains (S, E));
      pragma Assert (E = 1 or else E = 2 or else E = 3);

      declare
         Buffer : Set := S;
      begin
         while not Is_Empty (Buffer) loop
            E := Choose (Buffer);

            pragma Assert (Contains (S, E));
            pragma Assert (E = 1 or else E = 2 or else E = 3);

            Buffer := Remove (Buffer, E);

            pragma Loop_Variant (Decreases => Length (Buffer));
            pragma Loop_Invariant (Buffer <= S);
         end loop;
      end;
   end Test_Set;

begin

   --------------------------
   -- Test Choose for Maps --
   --------------------------

   Test_Maps;

   --------------------------
   -- Test Choose for Sets --
   --------------------------

   Test_Set;

end Test;
