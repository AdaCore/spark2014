package Glob is
   G : Boolean;
   procedure Sub;
   procedure P with
     Pre  => not G,
     Post => G;
end;
