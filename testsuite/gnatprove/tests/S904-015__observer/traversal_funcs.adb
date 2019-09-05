procedure Traversal_Funcs with SPARK_Mode is
   type List;
   type List_Acc is access List;
   type List is record
      V : Integer;
      N : List_Acc;
   end record;

   function Next (X : access constant List) return access constant List with Pre => True is
      C : access constant List := X;
   begin
      if C /= null then
         C := C.N;
      end if;
      return C;
   end Next;

   function Next_2 (X : access constant List) return access constant List with Pre => True is
      C : access constant List := Next (X);
   begin
      if C /= null and then Next (C.N) /= null then
         C := Next (C.N).N;
      end if;
      return C;
   end Next_2;

   procedure P (L : List_Acc; I : in out Integer) is
      Y : access constant List := Next (Next_2 (Next (L)));
   begin
      Y := Next_2 (Next (Y));
      if Y /= null then
         I := Y.V;
      end if;
   end P;
begin
   null;
end Traversal_Funcs;
