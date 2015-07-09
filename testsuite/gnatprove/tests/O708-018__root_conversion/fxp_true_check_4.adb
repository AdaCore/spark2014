with Common; use Common;

procedure Fxp_True_Check_3b is
   type My_Duration2 is new Duration range -20.0 .. 20.0;
   MD  : My_Duration  := -10.0;
   MD2 : My_Duration2 := +10.0;
begin
   pragma Assert (Duration (MD) = Duration (-MD2));
end;
