with Interfaces.C; use Interfaces.C;
with Square_Pack; use Square_Pack;
function Square (Arg : int) return int
is
	Result : int;
begin
	if Arg mod 2 = 0 then
		Result := Square_Even (Arg);
	else
		Result := Square_Odd (Arg);
	end if;
	return Result;
end;
