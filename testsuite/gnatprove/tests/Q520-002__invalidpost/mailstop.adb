with Ada.Text_IO;
with Names;

procedure MailStop is
begin
   if Names.Is_Domain_Name("lemuria.cis.vtc.edu") then
      Ada.Text_IO.Put_Line("It is a valid domain name [CORRECT]");
   else
      Ada.Text_IO.Put_Line("It is not a valid domain name [INCORRECT]");
   end if;
end MailStop;
