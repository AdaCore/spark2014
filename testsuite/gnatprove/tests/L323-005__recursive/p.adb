package body P is
    function Id (N : Natural) return Natural is (N);

    procedure Use_Bad is
    begin
       pragma Assert (Bad);
    end Use_Bad;

    procedure Use_Down (X : Positive) is
    begin
       null;
    end Use_Down;

end P;
