procedure Test_Eq with SPARK_Mode is
    function Non_Returning (I, J : Integer) return Boolean with
      Pre => True
    is
    begin
       while True loop
          null;
       end loop;
       return True;
    end Non_Returning;

    type R is record
       F : Integer := 0;
    end record;

    function "=" (X, Y : R) return Boolean is
      (Non_Returning (X.F, Y.F));

    type RR is record
       G : R;
    end record;

    function Bad (X, Y : RR) return Boolean is
      (X = Y);
    pragma Annotate (GNATprove, Terminating, Bad);

    X, Y : RR;
begin
    pragma Assert (Bad (X, Y));
end Test_Eq;
