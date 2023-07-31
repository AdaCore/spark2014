package Good_Pack with SPARK_Mode is
    type U64 is range 0 .. 2**64-1;
    function Square (arg : U64) return U64 with
	Pre => (arg <= 4294967295),
	Post => (Square'Result = arg * arg);
end Good_Pack;
