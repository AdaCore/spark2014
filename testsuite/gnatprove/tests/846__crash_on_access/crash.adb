procedure Crash with SPARK_Mode is
   type Cell;
   type List is access all Cell;
   type Cell is record
      Head : aliased Integer;
      Tail : List;
   end record;
   procedure Test (X : in out List);
   procedure Test (X : in out List) is
      Y : List := X.Tail.Tail;
   begin
      X.Tail.Tail := null;
      declare
         Z : access constant Cell := X.Tail.all'Access;
      begin
         null;
      end;
   end Test;
   procedure Test2;
   procedure Test2 is
      X : List := new Cell'(Head => 0, Tail => null);
   begin
      X := new Cell'(Head => 1, Tail => X);
      declare
         Y : List := X.Tail;
      begin
         X.Tail := new Cell'(Head => 2, Tail => null);
         declare
            Z : List := X.all'Access;
         begin
            null;
         end;
      end;
   end Test2;
begin
   null;
end Crash;
