package Outer is
   X : Integer;
   Y : Integer;
   package Inner is
      X : Boolean;
      function Get return Boolean is (X);
      function Get return Integer is (Outer.X + Outer.Y);
   end Inner;
end Outer;
