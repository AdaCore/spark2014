package P is

    function Zero return Integer is (0);

    protected type PT (J : Integer) is
       pragma Assert (J > 0);
    private
       X : Positive := Zero; --@RANGE_CHECK:FAIL
    end;

    PO : PT (-1);

end;
