procedure test5 is
  type T is (A, B, C);
  V : T;
  I : Integer;
begin
  case V is
  pragma List ( On );
  when A =>
     I := 1;
  when others =>
     I := 2;
  end case;
end test5;
