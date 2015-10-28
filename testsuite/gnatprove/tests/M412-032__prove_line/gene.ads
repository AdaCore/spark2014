generic
   type T is private;
   X : Integer;
package Gene is

   procedure P (Y : in out Integer)
      with Pre => X < Y;

end Gene;

