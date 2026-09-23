package R is
   generic
      with procedure P (X : in out Integer) is <> with Post => X = 0;
   package Inner is
   end Inner;

   generic
   package Outer is
      procedure P (X : in out Integer) with Post => X = 0;
      package D is new Inner;
   end Outer;
end R;
