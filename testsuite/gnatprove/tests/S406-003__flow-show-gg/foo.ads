package Foo is
   X : Integer;
   Y : Integer;
   package Inner is
      X : Boolean;
      function Get return Boolean is (X);
      function Get return Integer is (Foo.X + Foo.Y);
   end Inner;
end Foo;
