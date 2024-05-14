procedure Structural_Variant with SPARK_Mode, Always_Terminates => True is
   type Cell;
   type List is access Cell;
   type Cell is record
      Next : List;
   end record;

   function Extend (X : in out Cell) return Boolean
     with Side_Effects, Post => X.Next /= null;
   function Extend (X : in out Cell) return Boolean is
   begin
      return B : constant Boolean := X.Next = null do
         if B then
            X.Next := new Cell'(Next => null);
         end if;
      end return;
   end Extend;

   procedure Terminating (X : in out Cell)
     with Always_Terminates => True,
     Subprogram_Variant => (Structural => X),
     Post => False;
   procedure Terminating (X : in out Cell) is
      B : Boolean;
   begin
      B := Extend (X);
      Terminating (X.Next.all); --@SUBPROGRAM_VARIANT:FAIL
   end Terminating;

   X : Cell := (Next => null);
begin
   Terminating (X);
end Structural_Variant;
