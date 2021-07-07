procedure Bad_Raise with SPARK_Mode is
   procedure Do_Something_1 (X : Integer) with
     Import,
     Pre => (if (if X > 0 then Boolean'(raise Program_Error) else X > -100) then X mod 2 = 0);
   procedure Do_Something_2 (X : Integer) with
     Import,
     Pre => (case (if X = 0 then Integer'(raise Program_Error) else X mod 3) is
               when 0 => X < 100,
               when 1 => X < 200,
               when 2 => X < 300,
               when others => raise Program_Error);
begin
   null;
end Bad_Raise;
