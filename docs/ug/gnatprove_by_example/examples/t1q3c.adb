package body T1Q3C
  with SPARK_Mode
is

   procedure NextDay_A (Today : in Day; Tomorrow : out Day) is
   --  This is implementation (a) of NextDay, in which Day'Succ is used
   begin
      if Today = Sun then
         Tomorrow := Mon;
      else
         Tomorrow := Day'Succ (Today);
      end if;
   end NextDay_A;

   procedure NextDay_B (Today : in Day; Tomorrow : out Day) is
      --  This is implementation (b) of NextDay, in which a
      --  case-statement is used
   begin
      case Today is
         when Mon => Tomorrow := Tue;
         when Tue => Tomorrow := Wed;
         when Wed => Tomorrow := Thu;
         when Thu => Tomorrow := Fri;
         when Fri => Tomorrow := Sat;
         when Sat => Tomorrow := Sun;
         when Sun => Tomorrow := Mon;
      end case;
   end NextDay_B;

end T1Q3C;
