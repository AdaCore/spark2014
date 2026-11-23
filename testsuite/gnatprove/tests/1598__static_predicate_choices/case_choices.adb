procedure Case_Choices (V : Integer) with SPARK_Mode is
   subtype Even is Integer range 1 .. 4
     with Static_Predicate => Even in 2 | 4;
   C : constant Integer :=
     (case V is when Even range 2 .. 2 => 8, when others => 0);
   D : Integer;
begin
   pragma Assert (C = (if V = 2 then 8 else 0)); -- @ASSERT:PASS
   case V is
      when Even range 2 .. 2 => D := 8;
      when others => D := 0;
   end case;
   pragma Assert (D = (if V = 2 then 8 else 0)); -- @ASSERT:PASS
end Case_Choices;
