package body Discr with
  SPARK_Mode
is
   procedure P is
      procedure Local (X, Y : in out R);
      procedure Local (X, Y : in out R) is
      begin
         X.K := Y.K;  --  BAD
      end Local;
      X : R(0);
      Y : R(-1);
   begin
      Local (X, Y);
   end P;

end Discr;
