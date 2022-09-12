with Nonsparkpkg;
package body Sparkpkg with SPARK_Mode => On is
    function F1(A: Integer) return Integer is
        LV : Nonsparkpkg.Int32_t := 1;   -- can't use a type declared where SPARK_Mode => Off, however simple?
    begin
        return Integer(LV) + A;
    end F1;
    function F2(A: Integer) return Integer is
        type Err_T is new Nonsparkpkg.Int32_t; -- can't even reinstantiate it here??
        LV : Err_T := 1;
    begin
        return Integer(LV) - A;
    end F2;
    function F3(A: Integer) return Integer is
        type Lookalike_T is range Nonsparkpkg.Int32_t'First .. Nonsparkpkg.Int32_t'Last with Size => Nonsparkpkg.Int32_t'Size, Alignment => Nonsparkpkg.Int32_t'Alignment;
        LV : Lookalike_T := 1;
    begin
        return Integer(LV) * A;
    end F3;
end Sparkpkg;
