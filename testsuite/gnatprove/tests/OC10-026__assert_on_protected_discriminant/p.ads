package P is

    function Zero return Integer is (0);

    protected type PT (J : Integer) is
       --  pragma Assert (J > 0); --  no longer allowed by the front end
    private
       X : Positive := Zero; --@RANGE_CHECK:FAIL
    end;

    PO : PT (-1);

end;
