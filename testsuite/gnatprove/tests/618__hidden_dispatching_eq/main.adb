procedure Main with SPARK_Mode is
   package A is
      type T is private;
      function "=" (X : T; Y : T) return Boolean;
      function Make return T;
   private
      type T is tagged null record;
   end A;
   package body A is
      function "=" (X : T; Y : T) return Boolean is (True);
      function Make return T is (null record);
   end A;
   use A;
   X : T := Make;
begin
   pragma Assert (X = X);
end Main;
