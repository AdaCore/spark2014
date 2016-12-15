package Types with SPARK_Mode is

    type U (<>) is private;

private
    type U is array (Positive range <>) of Integer;

    subtype A2 is U (1 .. 10);

    function Check_A2 (X : A2) return Boolean is
       (X (X'First) = 0);

end Types;
