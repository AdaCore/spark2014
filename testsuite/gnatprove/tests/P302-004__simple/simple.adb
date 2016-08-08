package body Simple with
SPARK_Mode
is

    function My_Eq (X1, X2 : General_Strings.Bounded_String) return Boolean
    is (General_Strings."=" (X1, X2));

end Simple;
