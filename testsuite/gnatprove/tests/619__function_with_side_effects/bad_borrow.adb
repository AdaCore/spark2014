procedure Bad_Borrow with SPARK_Mode, Post => False is --@POSTCONDITION:FAIL
   X : aliased Integer := 0;
   function F (X : not null access Integer) return Boolean with Side_Effects,
     Pre => X.all < Integer'Last,
     Post => X.all = Integer'(X.all)'Old + 1;
   function F (X : not null access Integer) return Boolean is
   begin
      X.all := X.all + 1;
      return True;
   end F;
   B : Boolean;
begin
   declare
      Borrow : not null access Integer := X'Access;
   begin
      B := F (Borrow);
   end;
end Bad_Borrow;
