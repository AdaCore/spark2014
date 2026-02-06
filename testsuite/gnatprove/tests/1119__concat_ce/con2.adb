function Con2 (X : String; Y : String) return String
  with Pre => X'Length <= 32
is
begin
   return X & Y;
end;
