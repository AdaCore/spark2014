procedure Main with SPARK_Mode is

   --  The user defined equality on T1 cannot be used on T2 in SPARK as SPARK
   --  does not see the derivation.

   package P is
      type T1 is private;
      function "=" (X, Y : T1) return Boolean;
      type T2 is private;
   private
      pragma SPARK_Mode (Off);
      type T1 is null record;
      function "=" (X, Y : T1) return Boolean is (True);
      type T2 is new T1;
   end P;

begin
   null;
end Main;
