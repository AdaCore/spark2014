procedure Main with SPARK_Mode is
   X : Integer;

   type T (D : Integer) is null record;
   type P is access T;
   procedure Proc with Global => null, Pre => P'(new T (D => X + 1)) /= null is
   begin
      null;
   end Proc;
begin
   null;
end Main;
