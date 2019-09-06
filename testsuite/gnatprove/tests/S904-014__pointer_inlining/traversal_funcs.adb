procedure Traversal_Funcs with SPARK_Mode is
   type List;
   type List_Acc is access List;
   type List is record
      V : Integer;
      N : List_Acc;
   end record;

   function Next (X : access constant List) return access constant List is
      C : access constant List := X;
   begin
      return C;
   end Next;

   procedure P (L : List_Acc; I : in out Integer) is
      Y : access constant List := Next (Next (Next (L)));
   begin
      I := Y.V;
   end P;
begin
   null;
end Traversal_Funcs;
