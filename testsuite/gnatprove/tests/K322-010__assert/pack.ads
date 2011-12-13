package Pack is

   X : Integer := 10;

   pragma Assert (X > 0);

   function F return Boolean
     with Pre  => X > 0,
          Post => 1 / X > 0;

   procedure P
     with Pre  => X > 0,
          Post => 1 / X > 0;
end;
