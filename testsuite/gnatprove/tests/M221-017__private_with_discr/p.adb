package body P is
   function My_Capacity (L : My_T1) return Integer
   is
   begin
      return L.Capacity;
   end My_Capacity;
   function Identity1 (L : My_T1) return My_T1
   is
   begin
      return L;
   end Identity1;
   function Identity2 (L : T2) return T2
   is
   begin
      return L;
   end Identity2;
end;
