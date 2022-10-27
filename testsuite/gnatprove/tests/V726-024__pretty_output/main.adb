procedure Main with SPARK_Mode is
   type R is record
      F : aliased Integer;
   end record;

   generic
      X : in out R;
   procedure P;

   procedure P is
      type T is record
         F : access Integer;
      end record;

      Y : T := (F => X.F'Access);
   begin
      Y.F.all := Y.F.all + 1;
   end P;

   X : R := (F => 12);
   procedure Q is new P (X);
begin
   Q;
end Main;
