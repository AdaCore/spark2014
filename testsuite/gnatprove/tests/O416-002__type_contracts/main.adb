with Messages; use Messages;
with Communications; use Communications;
procedure Main with SPARK_Mode is
   A : Message_Arr :=
     ((Sent => "0000-12-25", Received => "0033-04-03"),
      (Sent => "0570-00-00", Received => "0632-06-08"));
   Coms : Communication (2); --  := Create (A);
begin
   null;
end Main;

--  with Days; use Days;
--  procedure Main is
--     D : T_Day := Monday;
--  begin
--     Next_T (D);
--  end Main;
