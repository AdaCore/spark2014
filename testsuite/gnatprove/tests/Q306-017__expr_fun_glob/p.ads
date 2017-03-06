package P is

   X : Integer := 0;

   function F return Boolean is (X = 0) with Global => null;

   function B return Boolean is (True) with Post => X = 0, Global => null;

end;
