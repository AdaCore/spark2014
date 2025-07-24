procedure Main with SPARK_Mode is
   generic
      with function F (X : Integer) return Boolean with
        Pre => X >= 0;
   package G is
   end G;

   function F (X : Integer) return Boolean is (True) with
     Pre => X > 0;

   package I is new G (F);

begin
   null;
end Main;
