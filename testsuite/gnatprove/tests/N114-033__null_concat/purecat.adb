procedure Purecat is
  X : string (1 .. 1000) := (others => 'X');

  procedure P (Y : String) with
    Global => (In_Out => X),
    Pre => X = Y and X(1) = 'X'
  is
  begin
     pragma Assert (X = Y);
     X (1) := '?';
     pragma Assert (X /= Y);
  end;
begin
  P ("" & X);
end Purecat;
