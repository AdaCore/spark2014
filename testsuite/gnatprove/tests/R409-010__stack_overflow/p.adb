--  This test exposes a faulty behavior for progressive mode. It should
--  have a behavior looking like per_path but it directly raises stack_overflow
--  exception. This test is built to investigate this issue.
procedure Ifstats (B : Boolean) with SPARK_Mode is
   X : Integer := 0;
begin
   if B then
      X := X + 1;
   end if;
   if B then
      X := X + 1;
   end if;
   if B then
      X := X + 1;
   end if;
   if B then
      X := X + 1;
   end if;
   if B then
      X := X + 1;
   end if;
   if B then
      X := X + 1;
   end if;
   if B then
      X := X + 1;
   end if;
   if B then
      X := X + 1;
   end if;
   if B then
      X := X + 1;
   end if;
   if B then
      X := X + 1;
   end if;
   if B then
      X := X + 1;
   end if;
   if B then
      X := X + 1;
   end if;
   if B then
      X := X + 1;
   end if;
   if B then
      X := X + 1;
   end if;
   if B then
      X := X + 1;
   end if;
   if B then
      X := X + 1;
   end if;
   if B then
      X := X + 1;
   end if;
   if B then
      X := X + 1;
   end if;
   pragma Assert (X < 5);
end Ifstats;
