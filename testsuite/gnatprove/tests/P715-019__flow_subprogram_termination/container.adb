with Ada.Text_IO; use Ada.Text_IO;

package body Container is

   -- OBJECTS

   Arr          : Array_T   := (My_Integer'Range => 3);
   My_Container : Container := (A =>  Arr);
   Position     : Cursor    := (Index => 0);

   -- HELPER FUNCTIONS FOR CONTAINER
   function First (C : Container) return Cursor is
      (Cursor'(Index => 1));

   function Has_Element (C : Container; P : Cursor) return Boolean is
      (P.Index in My_Integer'Range);

   function Next (C : Container; P : Cursor) return Cursor is
      (if P.Index < My_Integer'Last then Cursor'(Index => P.Index + 1)
       else Cursor'(Index => 0));

   function Element (C : Container; P : Cursor) return Integer is
      (C.A (P.Index));

  -- SUBPROGRAMS
   procedure Test3 (X : in out My_Integer;
                    My_Container : Container) is
   begin
      -- non terminating loop
      for E of My_Container loop
         -- terminating loop
         loop
            X := X + 1;
            pragma Loop_Variant (Increases => X);
            exit when X = 5;
         end loop;
         B := False;
      end loop;
   end Test3;

   procedure Test4 is
      Int  : My_Integer := 2;
      Cont : Container  := (A => (My_Integer'Range => 4));
   begin
      Test3 (Int, Cont);
   end Test4;

begin

   -- non terminating loop
   while X > 0 loop
      B := True;
      if X < My_Integer'Last then
         X := X + 1;
      end if;
   end loop;

   -- terminating loop
   while I < 10 loop
      pragma Loop_Invariant (R >= 100 - 10 * I);
      pragma Loop_Variant (Increases => I,
                           Decreases => R);
      R := R - I;
      I := I + 1;
   end loop;

   -- non terminating loop
   loop
      X := X + 1;
      exit when X < 0;
   end loop;

   -- terminating loop
   loop
      X := X + 1;
      pragma Loop_Variant (Increases => X);
      exit when X = 5;
   end loop;

   -- non terminating loop
   for E of My_Container loop
      B := False;
   end loop;

   -- non terminating loop
   for E of My_Container loop
      -- terminating loop
      loop
         X := X + 1;
         pragma Loop_Variant (Increases => X);
         exit when X = 5;
      end loop;
      B := False;
   end loop;

   -- terminating loop
   for E of My_Container loop
      B := True;
      R := R - 1;
      pragma Loop_Invariant (B);
      pragma Loop_Variant (Decreases => R);
      -- terminating loop (simple for)
      for I in My_Integer'Range loop
         X := X + 1;
         pragma Loop_Variant (Increases => I);
         pragma Loop_Variant (Increases => X);
      end loop;
   end loop;

end Container;
