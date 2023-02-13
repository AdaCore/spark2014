with Sets; use Sets;
with Keys; use Keys;

procedure Test with SPARK_Mode is

   use Sets_Pack;
   use Keys_Pack;

   S : Set (10);
begin
   Insert (S, 3);
   Insert (S, 4);

   Replace (S, 3, 5);
end Test;
