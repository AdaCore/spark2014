package body Simple
with SPARK_Mode
is

   function Sum_People (Alice, Bob : People) return Lifetime is
   begin
      pragma Assert (Alice.Height /= Bob.Height);
      return Alice.Age + Bob.Age;
   end Sum_People;

   procedure Check_Town (T : Town) is
      Total_Age : Integer := 0;
   begin
      for N in T.People'Range loop
         Total_Age := Total_Age + Integer (T.People (N).Age);
      end loop;
      pragma Assert (Total_Age < 420);
   end Check_Town;

   procedure Check_Record (R : My_Record) is
   begin
      for N in R.Data'Range loop
         pragma Assert (R.Data (N) /= 42);
      end loop;
   end Check_Record;

end Simple;
