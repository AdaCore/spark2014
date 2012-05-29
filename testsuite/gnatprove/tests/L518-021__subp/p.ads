package P is
    X : Integer;
    function F return Integer is (X);
    function G return Integer;
private
    function G return Integer is (X);
end P;
