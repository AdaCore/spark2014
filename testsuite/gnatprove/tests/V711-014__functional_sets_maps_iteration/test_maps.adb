with SPARK.Containers.Functional.Maps;

procedure Test_Maps with SPARK_Mode is
   package My_Maps is new SPARK.Containers.Functional.Maps (Integer, Integer);
   use My_Maps;

   Max : constant Integer := 100;

   M1 : Map;
   M2 : Map;
begin
   for I in 1 .. Max loop
      M1 := Add (M1, I, 0);
      pragma Loop_Invariant (for all K of M1 => K in 1 .. I);
      pragma Loop_Invariant (for all K in 1 .. I => Has_Key (M1, K));
   end loop;

   for C in Iterate (M1) loop
      pragma Loop_Variant (Decreases => Length (C));
      pragma Loop_Invariant (C <= M1);
      pragma Loop_Invariant (M2 <= M1);
      pragma Loop_Invariant
        (for all K of M2 => not Has_Key (C, K));
      pragma Loop_Invariant
        (for all K of M1 => Has_Key (C, K) or Has_Key (M2, K));
      M2 := Add (M2, Choose (C), Get (C, Choose (C)));
   end loop;

   if M1 /= M2 then
      raise Program_Error;
   end if;

end Test_Maps;
