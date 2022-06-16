pragma SPARK_Mode;
procedure Top is
   type X is access Integer;
   type T;
   type P is access T;
   type T is record
      C : X;
      N : P;
   end record;

   V : P := new T'(C => null, N => new T'(C => null, N => null));
   W : access T := V;
   U : X := W.C;
begin
   W := W.N;
   W.C := null;
end;
