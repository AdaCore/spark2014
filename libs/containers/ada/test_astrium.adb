with Common; use Common; use Common.DLL;
with Test_Astrium_1; use Test_Astrium_1;
--with Test_Astrium_2;
with Test_Astrium_3;

procedure Test_Astrium is
   Monitorings : List;
begin
   Monitorings.Append ((Failed => False, Active => False));
   Monitorings.Append ((Failed => False, Active => True));
   Monitorings.Append ((Failed => False, Active => False));

   pragma Assert (Test_Astrium_1.Test_Recovery (Monitorings) = None);

   Test_Astrium_3.Activate_First_Non_Active (Monitorings);
   Test_Astrium_3.Activate_First_Non_Active (Monitorings);
   Test_Astrium_3.Activate_First_Non_Active (Monitorings);

end Test_Astrium;
