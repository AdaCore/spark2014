package Concurrency_Example is

   type Data_T is array (1 .. 1000) of Integer;
   All_Zeroes : constant Data_T := (others => 0);
   All_Ones   : constant Data_T := (others => Integer'First);
   Data : Data_T := All_Zeroes;

   task Writer;
   task Reader;

end Concurrency_Example;
