with Ada.Unchecked_Deallocation;

package body Allocs is

   function Alloc_10 (V : Integer) return A is
      (A'(1 => new Integer'(V),
          2 => new Integer'(V),
          3 => new Integer'(V)));
   function Alloc_10 return A is
      (A'(1 => new Integer'(42),
          2 => new Integer'(42),
          3 => new Integer'(42)));

   procedure Free is new Ada.Unchecked_Deallocation (Integer, T);

   procedure Alloc (V : Integer; B : Boolean; Result : out T) is
      Tmp : T := new Integer'(V);
   begin
      if B then
         Free (Tmp);
         Result := new Integer'(V);
      else
         Result := Tmp;
      end if;
   end;

   function Alloc (B : Boolean) return T is
   begin
      if B then
         return new Integer'(42);
      end if;
      return null;
   end;

   procedure Alloc_10 (V : Integer; B : Boolean; Result : out A) is
      Tmp : A :=
        A'(1 => new Integer'(V),
           2 => new Integer'(V),
           3 => new Integer'(V));
   begin
      if B then
         Result := Tmp;
      else
         Free (Tmp(1));
         Free (Tmp(2));
         Free (Tmp(3));
         Result := Tmp;
      end if;
   end;

   function Alloc_10 (B : Boolean) return A is
      Tmp : A;
   begin
      if B then
         Tmp := A'(1 => new Integer'(42),
                   2 => new Integer'(42),
                   3 => new Integer'(42));
      end if;
      return Tmp;
   end;

end Allocs;
