with Composite_Cursors; use Composite_Cursors;
procedure Loop_Iterable with SPARK_Mode is
   C1 : Cont1 := (Length  => 10,
                  Content => (1 .. 10 => 1, others => 0));
   C2 : Cont2 := (Length  => 10,
                  Content => (1 .. 10 => 1, others => 0));
begin
   for E of C1 loop
      pragma Assert (E = 1);
   end loop;

   for E of C2 loop
      pragma Assert (E = 1);
   end loop;
end Loop_Iterable;
