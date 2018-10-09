with P;

procedure Main is
begin
   P.Write; --  this writes both the discriminant and component
   P.Write; --  so the previous call is ineffective

   P.Read_Write; --  this writes only the component
   P.Read_Write; --  so is the previous call effective or not?
end;
