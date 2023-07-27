procedure Non_Binary_Mod with SPARK_Mode is

   type Very_Small is mod 2 ** 16 - 1 with Annotate => (GNATprove, No_Wrap_Around);
   subtype Small_Nat is Natural range 0 .. 8;

   function Power_Bad (X : Very_Small; N : Small_Nat) return Very_Small is (X ** N) with -- @OVERFLOW_CHECK:FAIL
     Pre => X <= 4;

   function Power_Ok (X : Very_Small; N : Small_Nat) return Very_Small is (X ** N) with
     Pre => X <= 3;

begin
   null;
end Non_Binary_Mod;
