package P is

    protected type PT (J : Integer) is
       pragma Assert (J > 0);
    end;

    PO : PT (-1);

end;
