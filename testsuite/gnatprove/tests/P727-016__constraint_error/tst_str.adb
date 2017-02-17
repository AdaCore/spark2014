procedure Tst_str is

  -- Create a badly defined string.
  --  A valid String requires an index in range of Positive (1..)
  subtype My_Str is String(0..9);

  s : My_Str;
  C : Character;

begin
  s := "1234567890";
  c := s(0);
end Tst_Str;