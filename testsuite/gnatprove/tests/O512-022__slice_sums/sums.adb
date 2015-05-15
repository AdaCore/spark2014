package body Sums is

    function Sum (X : Vector; Bounds : Slice_Bounds) return Integer is
        Result : Integer := 0;
    begin
        for I in Index range Bounds.Lo .. Bounds.Hi loop
            Result := Result + X (I);
        end loop;
        return Result;
    end Sum;

end Sums;
