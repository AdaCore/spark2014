procedure fxp_div_int_res is

   function Div (D1, D2 : Duration) return Integer is
      (Integer (D1 / D2))
   with Pre => D2 /= 0.0;

   D1, D2 : Duration;

   R : Integer;

begin
   D1 := Duration'Small * 4;
   D2 := Duration'Small * 2;
   R  := Integer (D1 / Duration (Duration'Small));
   pragma Assert (R = 4);
   pragma Assert (Div (D1, D2) = 2);
end;
