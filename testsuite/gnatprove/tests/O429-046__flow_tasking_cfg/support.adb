package body Support is
   protected body Prot is
      procedure Add (X : Natural) is
      begin
         Summary := Summary + X;
      end Add;

      function Get return Natural is (Summary);
   end Prot;

   task body Rand_Task is
   begin
      Prot.Add (1);
   end Rand_Task;
end Support;
