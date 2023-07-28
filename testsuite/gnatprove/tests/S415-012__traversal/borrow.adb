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

   subtype Non_Null_List_Acc is not null List_Acc;

   function Next_Next (L : access List) return access List with
     Pre => L /= null and then L.N /= null;

   function Next_Next (L : access List) return access List is
      Res : access List := Non_Null_List_Acc (L.N).N;
   begin
      return Res;
   end Next_Next;

   procedure P (X : access List) is

      function Get return Integer with Pre => True is
         Y : access constant List := Next (Next (X));
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
