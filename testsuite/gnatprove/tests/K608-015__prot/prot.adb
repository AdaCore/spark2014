procedure Prot is
   pragma SPARK_Mode (Off);
   protected type Shared_Boolean (Init : Boolean := False) is
      function  Value return Boolean;
   private
      Val : Boolean := Init;
   end Shared_Boolean;

   protected body Shared_Boolean is
      function Value return Boolean is
      begin
         return Val;
      end Value;
   end Shared_Boolean;

   B : Shared_Boolean (False);
begin
   null;
end Prot;
