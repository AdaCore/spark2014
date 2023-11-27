package body Predefined with SPARK_Mode is

   procedure Add (L : in out List; E : Integer) is
   begin
      L := new List_Cell'(E, L);
   end Add;

   function Copy (L : List) return List is
   begin
      if L = null then
         return null;
      else
         return new List_Cell'(L.Data, Copy (L.Next));
      end if;
   end Copy;

end Predefined;
