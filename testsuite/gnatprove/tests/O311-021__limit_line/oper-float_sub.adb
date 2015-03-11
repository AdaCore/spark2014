separate (Oper)
procedure Float_Sub (X, Y : Float; Z : out Long_Float) is
begin
   Z := Long_Float(X) - Long_Float(Y);
end Float_Sub;
