procedure Proc (Length : Integer)
  with Global => null,
       Depends => (null => Length)
is
   subtype Index is Integer range 1 .. Length;
   My_Arr : Index;
begin
   My_Arr := Index'First;
end Proc;
