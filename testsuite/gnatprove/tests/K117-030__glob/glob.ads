package Glob is
   G : Boolean;
   procedure Sub;
   procedure P with
     Pre  => not G,
     Post => not G;
end;
