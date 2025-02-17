package body H with SPARK_Mode is

   function "=" (X, Y : T) return Boolean is
     (X.all = Y.all);

   procedure P (X : T) is
   begin
      if X.all = 0 then
         X.all := 1;
      else
         X.all := 0;
      end if;
   end P;

   procedure P2 (X, Y : T) is
   begin
      P (X);
   end P2;

   function Copy (X : T) return T is
      R : T := new Integer'(X.all);
   begin
      return R;
   end Copy;

   function New_T return T is
      R : T := new Integer'(0);
   begin
      return R;
   end New_T;

end H;
