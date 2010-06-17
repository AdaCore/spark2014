package body Tests is

   procedure Test1 (Li : in out List; C : in out Cursor) is
      N : Cursor := Next (C);
   begin
      if Has_Element (N) then
         Delete (Li, N);
      else
         Delete (Li, C);
      end if;
   end Test1;

   procedure Test2 (Li : in out List; E : Elem; Result : out Elem) is
      C : Cursor;
   begin
      Prepend (Li, E);
      C := Last (Li);
      Delete (Li, C);
      C := Next (First (Li));
      Delete (Li, C);
      C := Last (Li);
      Delete (Li, C);
      C := Last (Li);
      Delete (Li, C);
      Result := Element (Last (Li));
   end Test2;

   procedure Test3 (Li : in out List; C, D, F, G, H : Cursor; E : Elem) is
   begin
      Insert (Li, C, E);
      Append (Li, E);
      if Has_Element (D) then
         Insert (Li, D, E);
      end if;
      Insert (Li, F, E);
      if Length (Li) > 5 then
         if G = Next (C) then
            Insert (Li, G, E);
         else
            Insert (Li, H, E);
         end if;
      end if;
   end Test3;

   function Test4 (Li : List) return Count_Type is
      N : Count_Type := 0;
      C : Cursor     := First (Li);
   begin
      while Has_Element (C) loop
         N := N + 1;
         C := Next (C);
      end loop;
      return N;
   end Test4;

   procedure Test5 (Li : in out List; E : Elem) is
      C : Cursor := First (Li);
   begin
      while Has_Element (C) loop
         Insert (Li, C, E);
         C := Next (C);
      end loop;
   end Test5;

end Tests;
