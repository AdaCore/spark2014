procedure Foo with SPARK_Mode is
   E : exception;
   Index : Integer := 0;
   type A is array (Integer range <>) of Integer;
begin
   while Index < 1000 loop
      begin
         raise E;
      exception
         when E =>
            declare
               X : constant A := (Index .. Index => 42);
            begin
               pragma Assert (Index = 0);
            end;
      end;
      pragma Loop_Invariant (Index = 0);
      pragma Loop_Variant (Increases => Index);
      Index := Index + 1;
   end loop;
   pragma Assert (False);
end Foo;
