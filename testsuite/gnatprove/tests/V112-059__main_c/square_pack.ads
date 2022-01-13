with Interfaces.C; use Interfaces.C;
package Square_Pack
	with SPARK_Mode => On
is
	Max_Square_Arg : constant int := 46340;
	function Square_Even (Arg : int) return int with
		     Pre => (Arg mod 2 = 0) and then (Arg <= Max_Square_Arg)
		        and then (Arg >= -Max_Square_Arg),
		     Post => (Square_Even'Result = Arg * Arg),
		     Global => null,
		     Depends => (Square_Even'Result => Arg);
	function Square_Odd (Arg : int) return int with
		     Pre => (Arg mod 2 = 1) and then (Arg <= Max_Square_Arg)
		        and then (Arg >= -Max_Square_Arg),
		     Post => (Square_Odd'Result = Arg * Arg),
		     Global => null,
		     Depends => (Square_Odd'Result => Arg);
end Square_Pack;
