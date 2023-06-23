with SPARK.Big_Integers; use SPARK.Big_Integers;
with Ada.Unchecked_Deallocation;

procedure Main with SPARK_Mode is
   pragma Unevaluated_Use_Of_Old (Allow);
   type Cell;
   type List is access Cell;
   type Cell is record
      First :         Integer;
      Last  :         Integer;
      Tail  : aliased List;
   end record;

   procedure Free is new Ada.Unchecked_Deallocation (Cell, List);

   function Size (L : List) return Big_Natural is
     (if L = null then Big_Natural'(0) else 1 + Size (L.Tail))
       with Subprogram_Variant => (Structural => L),
       Post => True;

   procedure Ghost_Delete (X : in out List)
     with Ghost,
     Global => null,
     Depends => (X => null, null => X),
     Post => X = null,
     Always_Terminates;

   procedure Ghost_Delete (X : in out List) is
      procedure Free2 is new Ada.Unchecked_Deallocation (Cell, List);
   begin
      while X /= null loop
         pragma Loop_Variant (Decreases => Size (X));
         declare
            Tail : List := X.Tail;
         begin
            Free2 (X);
            X := Tail;
         end;
      end loop;
      Free2 (X);
   end;

   function Mem (L : List; E : Integer) return Boolean is
     (L /= null
      and then (E in L.First .. L.Last or else Mem (L.Tail, E)))
     with Subprogram_Variant => (Structural => L),
       Post => True;

   function Deep_Copy (L : List) return List
     with Subprogram_Variant => (Structural => L),
     Global => null,
     Post => (for all E in Integer => Mem (L, E) = Mem (Deep_Copy'Result,E));

   function Deep_Copy (L : List) return List is
   begin
      if L = null
      then
         return null;
      else
         return new Cell'(First => L.First,
                          Last  => L.Last,
                          Tail  => Deep_Copy (L.Tail));
      end if;
   end Deep_Copy;

   function At_End
     (L_Ptr : access constant List)
      return access constant List is (L_Ptr)
     with Ghost, Global => null, Annotate => (GNATprove, At_End_Borrow);

   procedure Split_In_Singletons (L : aliased in out List)
     with Post =>
       (for all E in Integer => Mem (Deep_Copy(L)'Old,E) = Mem (L,E)),
       Always_Terminates;

   procedure Split_In_Singletons (L : aliased in out List) is
      Init_Copy  : List := Deep_Copy (L) with Ghost;
      Cursor     : not null access List := L'Access;
      Outer_Save : constant not null access constant List :=
        At_End (Cursor) with Ghost;
   begin
      loop
         pragma Loop_Invariant
           (for all E in Integer =>
              (if Mem (Outer_Save.all, E)
               then Mem (Init_Copy, E) or else Mem (At_End (Cursor).all, E)));
         pragma Loop_Invariant
           (for all E in Integer =>
              (if Mem (At_End (Cursor).all, E)
               or else (Mem (Init_Copy, E) and then not Mem (Cursor.all, E))
               then Mem (Outer_Save.all, E)));
         pragma Loop_Invariant
           (for all E in Integer =>
              (if Mem (Cursor.all, E) then Mem (Init_Copy, E)));
         pragma Loop_Variant (Decreases => Size (Cursor.all));
         exit when Cursor.all = null;
         declare
            First : constant Integer := Cursor.all.First;
            Last  : constant Integer := Cursor.all.Last;
         begin
            if First > Last then
               declare
                  Tail : constant List := Cursor.all.Tail;
               begin
                  Free (Cursor.all);
                  Cursor.all := Tail;
               end;
            elsif First = Last then
               Cursor := Cursor.all.Tail'Access;
            else
               Cursor.all.Last := First;
               declare
                  Save : constant not null access constant List :=
                    At_End (Cursor) with Ghost;
                  Tail : constant List := Cursor.all.Tail;
               begin
                  Cursor.all.Tail := null;
                  Cursor := Cursor.all.Tail'Access;
                  for I in First + 1 .. Last loop
                     pragma Loop_Invariant (Cursor.all = null);
                     pragma Loop_Invariant
                       (for all E in Integer =>
                          Mem (Save.all, E) = (E in First .. (I-1)
                            or Mem (At_End (Cursor).all, E)));
                     Cursor.all :=
                       new Cell'(First => I, Last => I, Tail => null);
                     Cursor := Cursor.all.Tail'Access;
                  end loop;
                  Cursor.all := Tail;
               end;
            end if;
         end;
      end loop;
      Ghost_Delete (Init_Copy);
   end Split_In_Singletons;

begin
   null;
end Main;
