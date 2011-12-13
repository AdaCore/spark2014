with Ring_Buf; use Ring_Buf;

procedure Harness (X, Y, Z : Integer) is
   R : Ring_Buffer;
   H : Integer;
begin
   Clear (R);
   Push (R, X);
   Push (R, Y);
   Pop (R, H);
   pragma Assert (H = X);
   Push (R, Z);
   Pop (R, H);
   pragma Assert (H = Y);
   Pop (R, H);
   pragma Assert (H = Z);
end Harness;
