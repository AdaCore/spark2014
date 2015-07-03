package body Support is
   protected body Prot is
      procedure Add (X : Natural) is
      begin
         Summary := Summary + X;
      end Add;

      function Get return Natural is (Summary);
   end Prot;

   task body Rand_Task is
      Rand : Natural := Natural (Random_3.Random (G));
   begin
      Prot.Add (Rand);
   end Rand_Task;

begin
   Random_3.Reset (G);
end Support;
