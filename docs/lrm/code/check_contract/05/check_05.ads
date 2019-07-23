package Check_05
is
   subtype Small is Integer range 1 .. 10;
   subtype Big   is Integer range 1 .. 21;

   procedure Compare(A, B : in Small; C : in out Big);
end Check_05;
