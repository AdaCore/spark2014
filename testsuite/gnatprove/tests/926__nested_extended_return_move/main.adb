with Ada.Unchecked_Deallocation;
procedure Main with SPARK_Mode is
   type Cell;
   type List is access Cell;
   type Cell is record
      Head : Integer;
      Tail : List;
   end record;

   procedure Free is new Ada.Unchecked_Deallocation (Cell, List);

   Global : List := null;
   function Foo return List
     with Side_Effects,
     Global => (In_Out => Global),
     Pre => Global = null,
     Post => Global /= null and then Global.Head = 0 and then Global.Tail = null
       and then Foo'Result /= null and then Foo'Result.Head = 0 and then Foo'Result.Tail = null,
     Always_Terminates => True;

   function Foo return List is
   begin
      return Res : List := new Cell'(Head => 0, Tail => null)
      do
         Global := Res;
         return;
      end return;
   end Foo;

   Tmp : List := null;
begin
   Tmp := Foo;
   Global.Head := 1;
   pragma Assert (Tmp.Head = 0);
   Free (Global);
   Free (Tmp);
end Main;
