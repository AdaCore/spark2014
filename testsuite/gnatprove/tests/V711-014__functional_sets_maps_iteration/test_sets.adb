with SPARK.Containers.Functional.Sets;

procedure Test_Sets with SPARK_Mode is
   package My_Sets is new SPARK.Containers.Functional.Sets (Integer);
   use My_Sets;

   Max : constant Integer := 100;

   M1 : Set;
   M2 : Set;
begin
   for I in 1 .. Max loop
      M1 := Add (M1, I);
      pragma Loop_Invariant (for all K of M1 => K in 1 .. I);
      pragma Loop_Invariant (for all K in 1 .. I => Contains (M1, K));
   end loop;

   for C in Iterate (M1) loop
      pragma Loop_Variant (Decreases => Length (C));
      pragma Loop_Invariant (C <= M1);
      pragma Loop_Invariant (M2 <= M1);
      pragma Loop_Invariant
        (for all K of M2 => not Contains (C, K));
      pragma Loop_Invariant
        (for all K of M1 => Contains (C, K) or Contains (M2, K));
      M2 := Add (M2, Choose (C));
   end loop;

   if M1 /= M2 then
      raise Program_Error;
   end if;

end Test_Sets;
