with Update_Illegal_3; use Update_Illegal_3;

procedure Main is
   My_Discr_Rec : Discr_Record_T := Discr_Record_T'(Discr => True,
                                                    A => 1,
                                                    B => 2,
                                                    C => 3);
begin
   P1 (My_Discr_Rec);
end Main;
