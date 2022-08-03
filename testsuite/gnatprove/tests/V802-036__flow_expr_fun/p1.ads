package P1 with
    SPARK_Mode => On,
    Abstract_State => State
is

    function Get_X return Boolean;
    function Call_Get_X return Boolean is (Get_X);
    function Get_Y return Boolean;
    procedure Set_X_And_Y;

end P1;
