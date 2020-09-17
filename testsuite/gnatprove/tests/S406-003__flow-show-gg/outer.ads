package Outer is
   X : Integer;
   Y : Integer;
   package Inner is
      X : Boolean;
      function Get (A : Boolean;
                    B : Boolean)
                    return Boolean
      is
        (A = X)
        with Pre => A = True;
      function Get return Integer is (Outer.X + Outer.Y);
   end Inner;

end Outer;
