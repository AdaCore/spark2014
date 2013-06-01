package Pack is
    X : Integer;

    function Get_X return Integer is (X);

    function X_Is_Positive return Boolean is (X > 0);

    function Greater_Than_X (Y : Integer) return Boolean is (Y > X);

end Pack;
