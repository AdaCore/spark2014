package body P1 with
    SPARK_Mode => On,
    Refined_State => (State => (X, Y))
is

    X, Y : Boolean := False;

    function Get_X return Boolean is (X);
    function Get_Y return Boolean is (Y);

    procedure Set_X_And_Y is
    begin
        X := True;
        Y := True;
    end Set_X_And_Y;

end P1;
