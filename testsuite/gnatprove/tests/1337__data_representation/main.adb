procedure Main is
   type T is record
      C : Integer;
   end record;

   function "=" (X, Y : T) return Boolean
      with Pre => True
   is
      --  This data type will appear as "Main.""="".TT" in data representation
      --  file, with quotes around '=' escaped.

      type TT is record
         CC : Integer;
      end record;

      XX : TT := (CC => X.C);
      YY : TT := (CC => Y.C);
   begin
      return XX = YY;
   end;

   A, B : T := (C => 123);
begin
   if A = B then
      null;
   end if;
end;
