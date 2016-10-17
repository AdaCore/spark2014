package P is

    protected type PT is
       pragma Priority (10);
       function Dummy return Boolean;
    end;

    PO : PT;

    X : Integer := 0;

end;
