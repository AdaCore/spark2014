with P_Initial; use P_Initial;

procedure Q_Initial (T : Table; I, J : Index)
with
  Global => null,
  Pre => I in T'Range and then J in T'Range
is
begin
   if Is_Sorted (T)
     and then I < J
   then
      pragma Assert (T(I) <= T(J));
   end if;
end Q_Initial;
