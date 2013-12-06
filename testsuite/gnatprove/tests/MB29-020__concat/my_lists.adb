package body My_Lists is

   function Length (L : My_List) return Natural is
      Current : My_List := L;
      Result  : Natural := 0;
   begin
      while Current /= null loop
         Result := Result + 1;
         Current := Current.Tail;
      end loop;
      return Result;
   end Length;

   function Singleton (I : Integer) return My_List is
     (new My_List_Record'(Head => I, Tail => null));

   function Head (L : My_List) return Integer is
      (L.Head);

   function Cons (I : Integer; L : My_List) return My_List is
      (new My_List_Record'(Head => I, Tail => L));

   function Get_Model (L : My_List) return Int_Array is
      Current : My_List := L;
      Result  : Int_Array (1 .. Length (L));
   begin
      for I in Result'Range loop
         Result (I) := L.Head;
         Current := Current.Tail;
      end loop;
      return Result;
   end Get_Model;
end;
