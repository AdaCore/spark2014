procedure P is
  type T (X : Integer := 5) is record
    null;
  end record;

  X : T;

  Y : T(2) := T'(X => 2);

  function Int_Ident (X : Integer) return Integer
  is
  begin
    return X;
  end Int_Ident;

begin
  X := T'(X => Int_Ident(3));
  Y := T'(X => Int_Ident(3));
end P;
