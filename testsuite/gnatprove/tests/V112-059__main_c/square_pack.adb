with Interfaces.C; use Interfaces.C;
package body Square_Pack
	with SPARK_Mode => On
is
	function Square_Even (Arg : int) return int
	is
		Result : int;
	begin
		pragma Assert (Arg mod 2 = 0);
		Result := Arg * Arg;
		return Result;
	end;
	function Square_Odd (Arg : int) return int
	is
		Result : int;
	begin
		pragma Assert (Arg mod 2 = 1);
		Result := Arg * Arg;
		return Result;
	end;
end Square_Pack;
