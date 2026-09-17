pragma Ada_2022;

procedure Main with SPARK_Mode is

   -------------
   -- Generic --
   -------------

   generic
      type T is private;
      with function Guard (X : T) return Boolean;
      with function P (X : T) return Boolean
        with Pre => Guard (X);
      with function F (X : T) return Integer
        with Pre => Guard (X) and then P (X);
   package G is
      function Use_It (X : T) return Integer
        with Pre => Guard (X) and then P (X);
   end G;

   package body G is
      function Use_It (X : T) return Integer is (F (X));
   end G;

   --------------
   -- Instance --
   --------------

   type T is new Integer;

   function My_Guard (X : T) return Boolean is (X > 0);

   function My_P (X : T) return Boolean is (X > 1)
     with Pre => My_Guard (X);

   function My_F (X : T) return Integer is (Integer (X))
     with Pre => My_Guard (X) and then My_P (X);

   package My_G is new G (T, My_Guard, My_P, My_F);

begin
   null;
end Main;
