with General_Strings;

package Simple with
   SPARK_Mode
is

    function My_Eq (X1, X2 : General_Strings.Bounded_String) return Boolean
    with Global => null;

end Simple;
