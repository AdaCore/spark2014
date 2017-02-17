with Power_and_Sum; use Power_and_Sum;
with Ada.Text_IO; use Ada.Text_IO;
procedure Main is pragma SPARK_Mode (On);
   X : Integer := 2;
   N : Integer := 15;
   I : Positive := 1;
   Result : Integer;
   Result2: Integer;
begin
   --     Power(X, N, Result);

   while I <= N loop
      Sum(I, Result);
      Sum_Of_Sum(I, Result2);
      Put_Line ("Sum(" & Integer'Image (I) & " ) = " & Integer'Image (Result));
      Put_Line ("Sum_Of_Sum(" & Integer'Image (I) & " ) = " & Integer'Image (Result2));
      I := I + 1;
   end loop;

end Main;
