with CRTP_Pack; use CRTP_Pack;

procedure Console_Pack is
   procedure CRTP_Append_Character_Data is new CRTP_Append_Data (Character);
begin
   null;
end Console_Pack;
