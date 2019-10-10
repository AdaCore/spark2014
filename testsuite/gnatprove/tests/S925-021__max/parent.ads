package Parent is
   type Some_Type is private;

private
   type Some_Type is mod 2 ** 64;
end Parent;
