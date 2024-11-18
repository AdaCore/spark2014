procedure Test with SPARK_Mode is
   package Nested is
      procedure P1 (X : in out Integer) with
        Post => (if X'Old < Integer'Last then X > X'Old);
      procedure P2 (X : in out Integer) with
        Contract_Cases =>
          (X < Integer'Last => X > X'Old,
           others           => X = X'Old);
   end Nested;

   package body Nested is
      procedure P1 (X : in out Integer) with
        Refined_Post => X >= X'Old
      is
      begin
         if X < Integer'Last then
            X := X + 1;
         end if;
      end P1;
      procedure P2 (X : in out Integer) with
        Refined_Post => X >= X'Old
      is
      begin
         if X < Integer'Last then
            X := X + 1;
         end if;
      end P2;
   end Nested;
begin
   null;
end;
