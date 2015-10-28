package Account7 with
  SPARK_Mode
is
   protected type Protected_Natural is
      entry Incr;
      function Get return Natural;
   private
      The_Data : Natural := 0;
      Not_Full : Boolean := True;
   end Protected_Natural;

   Num_Accounts : Protected_Natural;
   Max_Accounts : constant Natural := 100;

   procedure Incr_Num_Accounts;

   protected type Bad is
      entry Bad_E;
      procedure Bad_P;
      function Bad_F return Natural;
   private
   end Bad;

   task type Account_Management with
     Global  => (In_Out => Num_Accounts),
     Depends => (Account_Management => Account_Management,
                 Num_Accounts => Num_Accounts);
end Account7;
