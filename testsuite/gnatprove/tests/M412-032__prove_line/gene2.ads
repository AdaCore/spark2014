package Gene2 is

   generic
      type T is private;
      X : Integer;
   procedure P (Y : in out Integer)
      with Pre => X < Y;

end Gene2;
