package body Task_Non_Term is

   task body My_Task is
      A : Integer := 1;
      F : Integer := 1;
      Tmp : Integer;
   begin
      while F < 1000 loop
         Tmp := F;
         F := A + F;
         A := Tmp;
      end loop;
   end My_Task;

   task body My_Task2 is
      A : Integer := 1;
      F : Integer := 1;
      Tmp : Integer;
   begin
      loop
         Tmp := F;
         F := A + F;
         A := Tmp;
      end loop;
   end My_Task2;

end Task_Non_Term;
