package body Types
is
   procedure Proc1 (Obj : in out T1)
   is begin
      Obj := Obj;
   end;

   procedure Proc2 (Obj : in out T2)
   is begin
      Obj := Obj;
   end;

   procedure Proc3 (Obj : in out T3)
   is begin
      Obj := Obj;
   end;

begin
   Proc2 (TO2);
end;
