procedure Foo with SPARK_Mode, Always_Terminates => True is
   type Cell;
   type List is access Cell;
   type Cell is record
      Next : List;
   end record;

   procedure Extend (X : in out Cell) with Post => X.Next /= null;
   procedure Extend (X : in out Cell) is
   begin
      if X.Next = null then
         X.Next := new Cell'(Next => null);
      end if;
   end Extend;

   procedure Terminating (X : in out Cell)
     with Always_Terminates => True,
     Subprogram_Variant => (Structural => X),
     Post => False;
   procedure Terminating (X : in out Cell) is
   begin
      Extend (X);
      Terminating (X.Next.all); --@SUBPROGRAM_VARIANT:FAIL
   end Terminating;

   X : Cell := (Next => null);
begin
   Terminating (X);
end Foo;
