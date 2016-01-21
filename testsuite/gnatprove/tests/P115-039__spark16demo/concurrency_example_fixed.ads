package Concurrency_Example_Fixed is

   type Data_T is array (1 .. 1000) of Integer;
   All_Zeroes : constant Data_T := (others => 0);
   All_Ones   : constant Data_T := (others => Integer'First);

   protected Data is
      function Get return Data_T;
      procedure Set (V : Data_T);
   private
      Value : Data_T := All_Zeroes;
   end Data;

   task Writer;
   task Reader;

end Concurrency_Example_Fixed;
