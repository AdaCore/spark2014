with SPARK.Containers.Functional.Maps;

procedure Test with SPARK_Mode is
   procedure Regular_String_Eq with
     Global => null
   is
      package My_Maps is new SPARK.Containers.Functional.Maps (Positive, String);

      S : My_Maps.Map;
   begin
      S := My_Maps.Add (S, 1, "toto");
      S := My_Maps.Add (S, 2, "tata");
      S := My_Maps.Add (S, 3, "titi");
      pragma Assert (for all K of S => My_Maps.Get (S, K)'First = 1);
      pragma Assert (for all K of S => My_Maps.Get (S, K)'Last = 4);
      S := My_Maps.Add (S, 4, "    ");
      S := My_Maps.Add (S, 5, "    ");
      S := My_Maps.Add (S, 6, "    ");
      S := My_Maps.Add (S, 7, "    ");
      pragma Assert (My_Maps.Get (S, 1) = "toto");
      pragma Assert (My_Maps.Get (S, 2) = "tata");
      pragma Assert (My_Maps.Get (S, 3) = "titi");
      pragma Assert (for all K of S => My_Maps.Get (S, K)'First = 1);
      pragma Assert (for all K of S => My_Maps.Get (S, K)'Last = 4);
   end Regular_String_Eq;

   procedure String_Eq_With_First with
     Global => null
   is
      function My_Eq (L, R : String) return Boolean is
        (L = R and L'First = R'First);
      package My_Maps is new SPARK.Containers.Functional.Maps (Positive, String, "=", My_Eq);

      S : My_Maps.Map;
   begin
      S := My_Maps.Add (S, 1, "toto");
      S := My_Maps.Add (S, 2, "tata");
      S := My_Maps.Add (S, 3, "titi");
      pragma Assert (for all K of S => My_Maps.Get (S, K)'First = 1);
      pragma Assert (for all K of S => My_Maps.Get (S, K)'Last = 4);
      S := My_Maps.Add (S, 4, "    ");
      S := My_Maps.Add (S, 5, "    ");
      S := My_Maps.Add (S, 6, "    ");
      S := My_Maps.Add (S, 7, "    ");
      pragma Assert (My_Maps.Get (S, 1) = "toto");
      pragma Assert (My_Maps.Get (S, 2) = "tata");
      pragma Assert (My_Maps.Get (S, 3) = "titi");
      pragma Assert (for all K of S => My_Maps.Get (S, K)'First = 1);
      pragma Assert (for all K of S => My_Maps.Get (S, K)'Last = 4);
   end String_Eq_With_First;
begin
   null;
end Test;
