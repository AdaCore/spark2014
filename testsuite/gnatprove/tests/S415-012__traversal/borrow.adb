procedure Borrow with SPARK_Mode is
   type List;
   type List_Acc is access List;
   type List is record
      V : Integer;
      N : List_Acc;
   end record;

   function Next (X : access List) return access List with Pre => True is
   begin
      return X.N;
   end Next;

   procedure P (X : access List) is

      function Get return Integer with Pre => True is
         Y : access List := Next (Next (X));
      begin
         return Y.V;
      end Get;

      function Get_2 return Integer with Pre => True is
         X : List_Acc;
         Y : access List := Next (Next (X));
      begin
         return Y.V;
      end Get_2;

      Y : access List := Next (Next (X));
   begin
      Y.V := 1;
   end P;
begin
   null;
end Borrow;
