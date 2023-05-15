procedure Q with SPARK_Mode is

    type R is record
       F : Integer := 0;
    end record;

    function "=" (X, Y : R) return Boolean with
      Post => True
    is
    begin
       loop
          null;
       end loop;
       return True;
    end "=";

    type RR is record
       G : R;
    end record;

    function Bad (X, Y : RR) return Boolean is
      (X = Y);

    X, Y : RR;
begin
    pragma Assert (Bad (X, Y));
end Q;
