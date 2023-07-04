procedure Main with SPARK_Mode is

   procedure Loops_Forever with
     No_Return,
     Exceptional_Cases => (others => False),
     Always_Terminates => False;

   procedure Loops_Forever is
   begin
      loop
         null;
      end loop;
   end Loops_Forever;

   procedure Loops_When_B (B : Boolean) with
     Post => not B,
     Always_Terminates => not B;

   procedure Loops_When_B (B : Boolean) is
   begin
      if B then
         Loops_Forever;
      end if;
   end Loops_When_B;

   procedure Terminates with
     Always_Terminates;

   procedure Terminates is
   begin
      Loops_When_B (False);
   end Terminates;

begin
   null;
end Main;
