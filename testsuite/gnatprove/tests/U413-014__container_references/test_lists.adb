with Ada.Containers; use Ada.Containers;
with Ada.Containers.Formal_Doubly_Linked_Lists;

procedure Test_Lists with SPARK_Mode is
   package Int_Lists is new Ada.Containers.Formal_Doubly_Linked_Lists (Integer);
   use Int_Lists;

   procedure Test (L : aliased in out List) with
     Pre => Length (L) = 4
     and then First_Element (L) = 1
     and then Element (L, Next (L, First (L))) = 2
     and then Element (L, Next (L, Next (L, First (L)))) = 3
     and then Element (L, Next (L, Next (L, Next (L, First (L))))) = 4
   is
      F : constant Cursor := Next (L, Next (L, First (L)));
   begin
      declare
         C : constant access constant Integer := Constant_Reference (L, F);
      begin
         pragma Assert (C.all = 3);
      end;
      declare
         L_Acc : access List := L'Access;
         E     : constant access Integer := Reference (L_Acc, F);
      begin
         pragma Assert (E.all = 3);
         E.all := 5;
      end;
      pragma Assert (Length (L) = 4);
      pragma Assert (First_Element (L) = 1);
      pragma Assert (Element (L, Next (L, First (L))) = 2);
      pragma Assert (Element (L, Next (L, Next (L, First (L)))) = 5);
      pragma Assert (Element (L, Next (L, Next (L, Next (L, First (L))))) = 4);
      pragma Assert (F = Next (L, Next (L, First (L))));
   end Test;

   L : aliased List (100);
begin
   Append (L, 1);
   Append (L, 2);
   Append (L, 3);
   Append (L, 4);
   Test (L);
end Test_Lists;
