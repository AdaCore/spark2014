package P is

   task type TT (X : Integer);

   protected type PT (X : Integer) is
      procedure Proc with Global => X;
   end;

end;
